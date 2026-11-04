/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootPartitionMoments

/-! # Actual typing and uniform Fourier moment bounds for the temporary tree input -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- A proved finite spatial coefficient for the actual translated root partition function. -/
@[expose] def treeRootPartitionSpatialBound (d K M : ℕ) (q : Fin d → ℤ) : ℝ :=
  Classical.choose (exists_spatialNorm_bound_treeRootPartition K M q)

theorem treeRootPartitionSpatialBound_pos (d K M : ℕ) (q : Fin d → ℤ) :
    0 < treeRootPartitionSpatialBound d K M q :=
  (Classical.choose_spec (exists_spatialNorm_bound_treeRootPartition K M q)).1

theorem spatialNorm_treeRootPartition_le (d K M : ℕ) (q : Fin d → ℤ) :
    Fourier.spatialNorm K M (treeRootPartition q) ≤ ENNReal.ofReal (treeRootPartitionSpatialBound d K M q) :=
  (Classical.choose_spec (exists_spatialNorm_bound_treeRootPartition K M q)).2

/-- Each actual augmented input family has finite source spatial norms. Their size is used
only for Fourier and Fubini typing, not for the uniform root-momentum estimate. -/
theorem exists_spatialNorm_bound_appendRootPartition {d m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ}
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    ∃ Bq : ℝ, 0 < Bq ∧ ∀ a, Fourier.spatialNorm K M (appendRootInput f (treeRootPartition q) a) ≤
      ENNReal.ofReal Bq := by
  let Bq := 1 + max B (treeRootPartitionSpatialBound d K M q)
  refine ⟨Bq, by dsimp only [Bq]; have h := treeRootPartitionSpatialBound_pos d K M q; positivity, ?_⟩
  intro a
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [appendRootInput, Fin.lastCases_last] using
      (spatialNorm_treeRootPartition_le d K M q).trans (ENNReal.ofReal_le_ofReal (by
        dsimp only [Bq]
        linarith only [le_max_right B (treeRootPartitionSpatialBound d K M q)]))
  · simpa only [appendRootInput, Fin.lastCases_castSucc] using
      (hf b).trans (ENNReal.ofReal_le_ofReal (by
        dsimp only [Bq]
        linarith only [le_max_left B (treeRootPartitionSpatialBound d K M q)]))

/-- One fixed coefficient controls the original inputs and the untranslated root partition. -/
@[expose] def treeAugmentedInputBound (d K M : ℕ) (B : ℝ) : ℝ :=
  max 1 (max B (treeRootPartitionSpatialBound d K M 0))

theorem treeAugmentedInputBound_pos (d K M : ℕ) (B : ℝ) : 0 < treeAugmentedInputBound d K M B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Actual augmented leaf Fourier moment totals have a uniform bound independent of the root
partition cell. Translation invariance, rather than a weighted norm of the translated input,
is what supplies this estimate. -/
theorem prod_leafFourierMomentTotal_appendRootPartition_le {d m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d + 1 + J ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    (∏ a : Fin (m + 1), leafFourierMomentTotal J (appendRootInput f (treeRootPartition q) a)) ≤
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) := by
  have hC : 0 ≤ leafMomentLocalizationConstant d J M := by
    unfold leafMomentLocalizationConstant
    exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg M))
  have hB' : B ≤ treeAugmentedInputBound d K M B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hroot : treeRootPartitionSpatialBound d K M 0 ≤ treeAugmentedInputBound d K M B :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hleaf (a : Fin (m + 1)) : leafFourierMomentTotal J (appendRootInput f (treeRootPartition q) a) ≤
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) := by
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp only [appendRootInput, Fin.lastCases_last]
      rw [leafFourierMomentTotal_treeRootPartition_translate]
      exact (leafFourierMomentTotal_le J hK hM (treeRootPartitionSpatialBound_pos d K M 0).le
        (spatialNorm_treeRootPartition_le d K M 0)).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hroot hC))
    · simp only [appendRootInput, Fin.lastCases_castSucc]
      exact (leafFourierMomentTotal_le J hK hM hB (hf b)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hB' hC))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod (s := Finset.univ) (fun a _ => hleaf a)

end WaveTurbulence.Incoh
