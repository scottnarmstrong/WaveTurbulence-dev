/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpectralFamily

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootSpectralMass` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Uniform actual derivative mass of all tree root-partition amplitudes -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The true single-root spectral envelope has a uniform mass independent of the root cell.
The translated root input's weighted spatial norm does not enter this bound. -/
theorem lintegral_treeRootSpectralEnvelope_leSpatial {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    (∫⁻ u, ENNReal.ofReal (treeRootSpectralEnvelopeSpatial J f S q u) ∂sourceCellMeasure S) ≤
      ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
        ENNReal.ofReal (maskedSourceSpatialConstantSpatial d (m + 1) J 0) * ENNReal.ofReal (C ^ n) *
          (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  have hm := measurable_maskedCellEnvelopeSpatial J 0 (appendRootInputSpatial f (treeRootPartitionSpatial q)) S (by omega) hBq.le hq
  have hmass := lintegral_maskedCellEnvelope_zero_le_actual_totalsSpatial J
    (appendRootInputSpatial f (treeRootPartitionSpatial q)) S hS hK hBq.le hq
  have hprod := prod_leafFourierMomentTotal_appendRootPartition_leSpatial J f hK hM hB hf q
  have he (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
      ENNReal.ofReal (treeRootSpectralEnvelopeSpatial J f S q u) =
        ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J) *
          ENNReal.ofReal (maskedCellEnvelopeSpatial J 0 (appendRootInputSpatial f (treeRootPartitionSpatial q)) S u) :=
    ENNReal.ofReal_mul (treeRootAmplitudeDerivativeFactor_nonnegSpatial _ _)
  simp_rw [he]
  rw [lintegral_const_mul _ (show Measurable (fun u => ENNReal.ofReal (maskedCellEnvelopeSpatial J 0 (appendRootInputSpatial f (treeRootPartitionSpatial q)) S u)) from ENNReal.measurable_ofReal.comp hm)]
  have hbound := hmass.trans (mul_le_mul' le_rfl (mul_le_mul' hprod le_rfl))
  simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (treeRootAmplitudeDerivativeFactorSpatial d J))) hbound

end WaveTurbulence.Flower.IncTop