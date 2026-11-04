/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootSpectralFamily

/-! # Uniform actual derivative mass of all tree root-partition amplitudes -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The true single-root spectral envelope has a uniform mass independent of the root cell.
The translated root input's weighted spatial norm does not enter this bound. -/
theorem lintegral_treeRootSpectralEnvelope_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    (∫⁻ u, ENNReal.ofReal (treeRootSpectralEnvelope J f S q u) ∂sourceCellMeasure S) ≤
      ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J) *
        ENNReal.ofReal (maskedSourceSpatialConstant d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  have hm := measurable_maskedCellEnvelope J 0 (appendRootInput f (treeRootPartition q)) S (by omega) hBq.le hq
  have hmass := lintegral_maskedCellEnvelope_zero_le_actual_totals J
    (appendRootInput f (treeRootPartition q)) S hS hK hBq.le hq
  have hprod := prod_leafFourierMomentTotal_appendRootPartition_le J f hK hM hB hf q
  have he (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
      ENNReal.ofReal (treeRootSpectralEnvelope J f S q u) =
        ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J) *
          ENNReal.ofReal (maskedCellEnvelope J 0 (appendRootInput f (treeRootPartition q)) S u) :=
    ENNReal.ofReal_mul (treeRootAmplitudeDerivativeFactor_nonneg _ _)
  simp_rw [he]
  rw [lintegral_const_mul _ (show Measurable (fun u => ENNReal.ofReal (maskedCellEnvelope J 0 (appendRootInput f (treeRootPartition q)) S u)) from ENNReal.measurable_ofReal.comp hm)]
  have hbound := hmass.trans (mul_le_mul' le_rfl (mul_le_mul' hprod le_rfl))
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J))) hbound

end WaveTurbulence.Incoh
