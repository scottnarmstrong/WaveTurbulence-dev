/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceAmplitudeDerivative

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceAmplitudeDerivativeMeasurable` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual source amplitude derivative continuity in spectral variables -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact actual derivative formula separating the computed frequency and source coefficient. -/
theorem MomentumTreeData.iteratedFDeriv_sourceSpectralAmplitudeSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (k : Mom d) (j : ℕ) :
    iteratedFDeriv ℝ j (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k =
      (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z 0 ξ •
        iteratedFDeriv ℝ j (fun k : Mom d =>
          (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ)) k := by
  rw [(MomentumTreeData.sourceSpectralAmplitude_eq_const_modulationSpatial (P := P)),
    iteratedFDeriv_const_smul_apply' ((contDiff_momentumModulation (P.spectralShift ξ none)).of_le
      (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  simp only [sourceSpectralAmplitudeSpatial, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual operator derivatives have the joint spectral measurability needed by dominated
parameter differentiation, derived from finite source input smoothness. -/
theorem MomentumTreeData.continuous_spectral_sourceAmplitudeDerivativeSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) (j : ℕ) :
    Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ =>
      iteratedFDeriv ℝ j (fun k => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ) k) := by
  simp_rw [(MomentumTreeData.iteratedFDeriv_sourceSpectralAmplitudeSpatial (P := P))]
  exact ((MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P)) ζ f c z hK hB h 0).smul
    ((continuous_iteratedFDeriv_momentumModulation_frequency k j).comp ((MomentumTreeData.continuous_spectralShiftSpatial (P := P)) none))

end WaveTurbulence.Flower.IncTop