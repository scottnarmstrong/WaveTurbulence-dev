/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeAugmentedFrequencyRows
public import WaveTurbulence.Foundations.RegAsymp.TreeLeafProfiles

/-! # Order-uniform moment budget for the literal augmented-leaf tree modulation -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Incoh IncohInst WithLp

/-- Polynomial loss from the actual original integer momentum rows. -/
def treeSpectralFrequencyLoss (X : RegChain) (ζ : ℤˣ) : ℝ :=
  1+2*((X.treeLinks ζ).length:ℝ)*(1+(X.size:ℝ))

theorem one_le_treeSpectralFrequencyLoss (X : RegChain) (ζ : ℤˣ) :
    1 ≤ treeSpectralFrequencyLoss X ζ := by
  unfold treeSpectralFrequencyLoss
  exact le_add_of_nonneg_right (by positivity)

/-- Leaf-only shifts need just one independent leaf frequency moment. -/
theorem norm_tree_augmented_leafFrequency_le {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G)
    (α : Fin (Fintype.card (TPlus G)+1) → Mom d)
    (j : MomentumCoordinate (X.treeLinks (G.sig 0)).length) :
    ‖treeLeafFrequency (treeCarrier hX).withRootInput α j‖ ≤
      (1+(X.size:ℝ)) * ∑ a, ‖α a‖ := by
  unfold treeLeafFrequency
  calc
    _ ≤ ∑ a, ‖(treeCarrier hX).withRootInput.inputRow a j • α a‖ := norm_sum_le _ _
    _ ≤ ∑ a, (1+(X.size:ℝ))*‖α a‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Int.norm_cast_real]
      exact mul_le_mul_of_nonneg_right (norm_tree_augmented_profileRow_le hX (.inl a) j) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual NT linear shift is controlled by a polynomial in source order times a
single leaf-frequency moment. The link cutoffs have not been Fourier expanded. -/
theorem tree_leaf_modulation_weight_le {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) :
    1+((∑ j, ‖treeLeafFrequency (treeCarrier hX).withRootInput
      (fun a => toLp 2 (α a)) (some (j,0))‖)+
      (∑ j, ‖treeLeafFrequency (treeCarrier hX).withRootInput
        (fun a => toLp 2 (α a)) (some (j,1))‖)) ≤
      treeSpectralFrequencyLoss X (G.sig 0)*(1+∑ a, ‖toLp 2 (α a)‖) := by
  let S := ∑ a, ‖toLp 2 (α a)‖
  let A := 1+(X.size:ℝ)
  have hs (i : Fin 2) : (∑ j, ‖treeLeafFrequency (treeCarrier hX).withRootInput
      (fun a => toLp 2 (α a)) (some (j,i))‖) ≤ ((X.treeLinks (G.sig 0)).length:ℝ)*(A*S) := by
    calc
      _ ≤ ∑ _j : Fin (X.treeLinks (G.sig 0)).length, A*S := Finset.sum_le_sum
        (fun j _ => norm_tree_augmented_leafFrequency_le hX _ _)
      _ = _ := by simp
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hn : 0 ≤ ((X.treeLinks (G.sig 0)).length:ℝ) := Nat.cast_nonneg _
  have h0 := hs 0
  have h1 := hs 1
  change 1+(_+_) ≤ (1+2*((X.treeLinks (G.sig 0)).length:ℝ)*A)*(1+S)
  nlinarith only [h0,h1,hS,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hn) hA]

end WaveTurbulence.RegAsymp
