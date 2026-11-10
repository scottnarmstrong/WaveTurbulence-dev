/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootPartitionMoments

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeAugmentedInputBounds` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Actual typing and uniform Fourier moment bounds for the temporary tree input -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- A proved finite spatial coefficient for the actual translated root partition function. -/
@[expose] def treeRootPartitionSpatialBoundSpatial (d K M : ℕ) (q : Fin d → ℤ) : ℝ :=
  Classical.choose (exists_spatialNorm_bound_treeRootPartitionSpatial K M q)

theorem treeRootPartitionSpatialBound_posSpatial (d K M : ℕ) (q : Fin d → ℤ) :
    0 < treeRootPartitionSpatialBoundSpatial d K M q :=
  (Classical.choose_spec (exists_spatialNorm_bound_treeRootPartitionSpatial K M q)).1

theorem spatialNorm_treeRootPartition_leSpatial (d K M : ℕ) (q : Fin d → ℤ) :
    Fourier.spatialNorm K M (treeRootPartitionSpatial q) ≤ ENNReal.ofReal (treeRootPartitionSpatialBoundSpatial d K M q) :=
  (Classical.choose_spec (exists_spatialNorm_bound_treeRootPartitionSpatial K M q)).2

/-- Each actual augmented input family has finite source spatial norms. Their size is used
only for Fourier and Fubini typing, not for the uniform root-momentum estimate. -/
theorem exists_spatialNorm_bound_appendRootPartitionSpatial {d m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ}
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    ∃ Bq : ℝ, 0 < Bq ∧ ∀ a, Fourier.spatialNorm K M (appendRootInputSpatial f (treeRootPartitionSpatial q) a) ≤
      ENNReal.ofReal Bq := by
  let Bq := 1 + max B (treeRootPartitionSpatialBoundSpatial d K M q)
  refine ⟨Bq, by dsimp only [Bq]; have h := treeRootPartitionSpatialBound_posSpatial d K M q; positivity, ?_⟩
  intro a
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [appendRootInputSpatial, Fin.lastCases_last] using
      (spatialNorm_treeRootPartition_leSpatial d K M q).trans (ENNReal.ofReal_le_ofReal (by
        dsimp only [Bq]
        linarith only [le_max_right B (treeRootPartitionSpatialBoundSpatial d K M q)]))
  · simpa only [appendRootInputSpatial, Fin.lastCases_castSucc] using
      (hf b).trans (ENNReal.ofReal_le_ofReal (by
        dsimp only [Bq]
        linarith only [le_max_left B (treeRootPartitionSpatialBoundSpatial d K M q)]))

/-- One fixed coefficient controls the original inputs and the untranslated root partition. -/
@[expose] def treeAugmentedInputBoundSpatial (d K M : ℕ) (B : ℝ) : ℝ :=
  max 1 (max B (treeRootPartitionSpatialBoundSpatial d K M 0))

/-- Actual augmented leaf Fourier moment totals have a uniform bound independent of the root
partition cell. Translation invariance, rather than a weighted norm of the translated input,
is what supplies this estimate. -/
theorem prod_leafFourierMomentTotal_appendRootPartition_leSpatial {d m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    (∏ a : Fin (m + 1), leafFourierMomentTotal J (appendRootInputSpatial f (treeRootPartitionSpatial q) a)) ≤
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) ^ (m + 1) := by
  have hC : 0 ≤ leafMomentLocalizationConstant d J M := by
    unfold leafMomentLocalizationConstant
    exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg M))
  have hB' : B ≤ treeAugmentedInputBoundSpatial d K M B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hroot : treeRootPartitionSpatialBoundSpatial d K M 0 ≤ treeAugmentedInputBoundSpatial d K M B :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hleaf (a : Fin (m + 1)) : leafFourierMomentTotal J (appendRootInputSpatial f (treeRootPartitionSpatial q) a) ≤
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBoundSpatial d K M B) := by
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp only [appendRootInputSpatial, Fin.lastCases_last]
      rw [leafFourierMomentTotal_treeRootPartition_translateSpatial]
      exact (leafFourierMomentTotal_le J hK hM (treeRootPartitionSpatialBound_posSpatial d K M 0).le
        (spatialNorm_treeRootPartition_leSpatial d K M 0)).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hroot hC))
    · simp only [appendRootInputSpatial, Fin.lastCases_castSucc]
      exact (leafFourierMomentTotal_le J hK hM hB (hf b)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hB' hC))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod (s := Finset.univ) (fun a _ => hleaf a)

end WaveTurbulence.Flower.IncTop