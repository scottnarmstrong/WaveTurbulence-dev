/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedCellFamily
public import WaveTurbulence.Foundations.Incoh.TreeRootPartition
public import WaveTurbulence.Foundations.Incoh.SmoothModulatedDerivative
public import WaveTurbulence.Foundations.Incoh.UniformDerivativeProduct

/-! # Actual single-root spectral amplitudes and their full derivative envelope -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- An actual source spectral amplitude confined to one fixed root cell. -/
@[expose] def MomentumTreeData.rootCutoffSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  treeRootCutoff q k * P.allCellMaskedSpectralAmplitude ζ f S k u

/-- Uniform dimensional derivative cost of the extra root cutoff. -/
@[expose] def treeRootAmplitudeDerivativeFactor (d J : ℕ) : ℝ :=
  (2 : ℝ) ^ J * rootMaskDerivativeConstant d J

theorem treeRootAmplitudeDerivativeFactor_nonneg (d J : ℕ) : 0 ≤ treeRootAmplitudeDerivativeFactor d J :=
  mul_nonneg (by positivity) (zero_le_one.trans (one_le_rootMaskDerivativeConstant d J))

theorem MomentumTreeData.contDiff_rootCutoffSpectralAmplitude {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
    ContDiff ℝ ∞ (fun k => P.rootCutoffSpectralAmplitude ζ f S q k u) :=
  (contDiff_treeRootCutoff q).mul (P.contDiff_allCellMaskedSpectralAmplitude ζ f S u)

/-- Every actual derivative has an envelope given by the actual source Fourier moments. -/
theorem MomentumTreeData.norm_iteratedFDeriv_rootCutoffSpectralAmplitude_le {d n m w J j : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (hj : j ≤ J) (k : Mom d)
    (u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (fun k => P.rootCutoffSpectralAmplitude ζ f S q k u) k‖ ≤
      treeRootAmplitudeDerivativeFactor d J * maskedCellEnvelope J 0 f S u := by
  apply norm_iteratedFDeriv_mul_le_uniform (contDiff_treeRootCutoff q)
    (P.contDiff_allCellMaskedSpectralAmplitude ζ f S u)
    (zero_le_one.trans (one_le_rootMaskDerivativeConstant d J)) (maskedCellEnvelope_nonneg J 0 f S u)
    (fun i hi x => ?_) (fun i hi x => ?_) hj k
  · have hc : NTSP.chiDerivConst d i ≤ rootMaskDerivativeConstant d J := by
      unfold rootMaskDerivativeConstant
      have h := Finset.single_le_sum (fun a _ => NTSP.chiDerivConst_nonneg d a)
        (Finset.mem_range.mpr (by omega : i < J + 1))
      linarith only [h]
    exact (norm_iteratedFDeriv_treeRootCutoff_le q i x).trans hc
  · have h := P.weighted_norm_allCellMaskedAmplitudeDerivative_le ζ f S (W := 0) hi x u
    simpa only [pow_zero, one_mul] using h

/-- Actual single-root derivative slices are strongly measurable on the counted spectral space. -/
theorem MomentumTreeData.stronglyMeasurable_rootCutoffAmplitudeDerivative {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ) =>
      iteratedFDeriv ℝ j (fun k => P.rootCutoffSpectralAmplitude ζ f S q k u) k) := by
  change StronglyMeasurable (Function.uncurry (fun (u : SourceCellIndex S) ξ =>
    iteratedFDeriv ℝ j (fun k => P.rootCutoffSpectralAmplitude ζ f S q k (u, ξ)) k))
  apply stronglyMeasurable_countable_slices
  intro u
  let ψ := fun k : Mom d => treeRootCutoff q k * sourceRootMask u.1 k
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_treeRootCutoff q).mul (contDiff_sourceRootMask u.1)
  have he (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      (fun k => P.rootCutoffSpectralAmplitude ζ f S q k (u, ξ)) =
        fun k => ψ k * (P.sourceSpectralAmplitude ζ f u.1 u.2.val 0 ξ *
          (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ)) := by
    funext k
    simp only [rootCutoffSpectralAmplitude, allCellMaskedSpectralAmplitude,
      maskedSourceSpectralAmplitude, sourceSpectralAmplitude, inner_zero_right,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one, ψ]
    ring
  simp_rw [he]
  exact (continuous_iteratedFDeriv_smooth_modulated ψ hψ
    (P.sourceSpectralAmplitude ζ f u.1 u.2.val 0)
    (P.continuous_sourceSpectralAmplitude ζ f u.1 u.2.val hK hB hf 0)
    (fun ξ => P.spectralShift ξ none) (P.continuous_spectralShift none) k j)

end WaveTurbulence.Incoh
