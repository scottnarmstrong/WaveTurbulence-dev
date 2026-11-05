/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFrequencyRows
public import WaveTurbulence.Foundations.Incoh.MomentumTreeRootInput
public import WaveTurbulence.Foundations.Incoh.MomentumSpectralShift

/-! # Actual augmented tree Fourier shifts, including the moving root partition -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh IncohInst WithLp

private theorem norm_tree_unitRow_le {n : ℕ} (i j : MomentumCoordinate n) :
    ‖momentumUnitRow i j‖ ≤ (1:ℝ) := by
  unfold momentumUnitRow
  split <;> norm_num

/-- Adding the root input and the link cutoffs preserves the proved source row bound. -/
theorem norm_tree_augmented_profileRow_le {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G)
    (i : LocalizedCellIndex (X.treeLinks (G.sig 0)).length (Fintype.card (TPlus G)+1))
    (j : MomentumCoordinate (X.treeLinks (G.sig 0)).length) :
    ‖(treeCarrier hX).withRootInput.profileRow i j‖ ≤ 1+(X.size:ℝ) := by
  cases i with
  | inl a =>
    refine Fin.lastCases ?_ (fun b => ?_) a
    · change ‖(treeCarrier hX).withRootInput.inputRow (Fin.last (Fintype.card (TPlus G))) j‖ ≤ _
      simp only [MomentumTreeData.withRootInput, Fin.lastCases_last]
      exact (norm_tree_unitRow_le _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    · change ‖(treeCarrier hX).withRootInput.inputRow b.castSucc j‖ ≤ _
      simp only [MomentumTreeData.withRootInput, Fin.lastCases_castSucc]
      exact norm_treeNodeRow_le hX _ j
  | inr p =>
    change ‖momentumUnitRow (some p) j‖ ≤ _
    exact (norm_tree_unitRow_le _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))

/-- The actual localized Fourier shifts have only a linear loss in tree order. -/
theorem norm_tree_augmented_spectralShift_le {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G)
    (ξ : LocalizedCellIndex (X.treeLinks (G.sig 0)).length (Fintype.card (TPlus G)+1) → Fin d → ℝ)
    (j : MomentumCoordinate (X.treeLinks (G.sig 0)).length) :
    ‖(treeCarrier hX).withRootInput.spectralShift ξ j‖ ≤
      (1+(X.size:ℝ)) * ∑ i, ‖toLp 2 (ξ i)‖ := by
  unfold MomentumTreeData.spectralShift
  calc
    _ ≤ ∑ i, ‖(treeCarrier hX).withRootInput.profileRow i j • toLp 2 (ξ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (1+(X.size:ℝ))*‖toLp 2 (ξ i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Int.norm_cast_real]
      exact mul_le_mul_of_nonneg_right (norm_tree_augmented_profileRow_le hX i j) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end WaveTurbulence.RegAsymp
