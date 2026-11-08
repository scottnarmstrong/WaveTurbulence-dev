/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceRootMaskBounds
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAmplitudeDerivativeMeasurable
public import WaveTurbulence.Foundations.Incoh.ParameterIteratedDerivative
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedSourceAmplitude` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual smooth root-masked source spectral amplitudes -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual source spectral amplitude with the fixed leaf-center root mask. -/
@[expose] def MomentumTreeData.maskedSourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  sourceRootMask c k * (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual masked amplitude remains smooth at every momentum. -/
theorem MomentumTreeData.contDiff_maskedSourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    ContDiff ℝ ∞ (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) :=
  (contDiff_sourceRootMask c).mul ((MomentumTreeData.contDiff_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z ξ)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual derivatives of the masked source family are spectrally continuous. -/
theorem MomentumTreeData.continuous_spectral_maskedSourceAmplitudeDerivativeSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) (j : ℕ) :
    Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k) := by
  let g := fun v k : Mom d => sourceRootMask c k * (Real.fourierChar (inner ℝ v k) : ℂ)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    have hp : ContDiff ℝ ∞ (fun p : Mom d × Mom d => (Real.fourierChar (inner ℝ p.1 p.2) : ℂ)) := by
      simp_rw [Real.fourierChar_apply]
      have hr : ContDiff ℝ ∞ (fun p : Mom d × Mom d => 2 * Real.pi * inner ℝ p.1 p.2) :=
        contDiff_const.mul (contDiff_fst.inner ℝ contDiff_snd)
      have hc : ContDiff ℝ ∞ (fun p : Mom d × Mom d => ((2 * Real.pi * inner ℝ p.1 p.2 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hr
      exact (hc.mul contDiff_const).cexp
    exact ((contDiff_sourceRootMask c).comp contDiff_snd).mul hp
  have hD := (contDiff_parameter_iteratedFDeriv g hg j).continuous
  have he (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) =
        fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z 0 ξ • g (P.spectralShift ξ none) k := by
    funext k
    simp only [maskedSourceSpectralAmplitudeSpatial, sourceSpectralAmplitudeSpatial, inner_zero_right,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one, g, smul_eq_mul]
    ring
  have hgj (v : Mom d) : ContDiff ℝ ∞ (g v) := hg.comp (f := fun y : Mom d => (v, y)) (contDiff_const.prodMk contDiff_id)
  have hder (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      iteratedFDeriv ℝ j (fun k => (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k =
        (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z 0 ξ • iteratedFDeriv ℝ j (g (P.spectralShift ξ none)) k := by
    rw [he]
    exact iteratedFDeriv_const_smul_apply' ((hgj _).of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
  simp_rw [hder]
  have hmap : Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ => (P.spectralShift ξ none, k)) :=
    ((MomentumTreeData.continuous_spectralShiftSpatial (P := P)) none).prodMk continuous_const
  have hpartial : Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      iteratedFDeriv ℝ j (g (P.spectralShift ξ none)) k) :=
    hD.comp (f := fun ξ : LocalizedCellIndex n m → Fin d → ℝ => (P.spectralShift ξ none, k)) hmap
  exact ((MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z hK hB h 0).smul hpartial

end WaveTurbulence.Flower.IncTop