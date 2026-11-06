/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RelativeLeafControl
/-! Finite modification-cost sums preserve the full baseline leaf product. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped ENNReal

 theorem relative_leaf_cost_product_pos {w : ℕ} (LG : LayeredGarden w)
    (S : Finset (ActualInputLeaves LG.garden)) (B : (Fin w × TTree.Path) → NNReal) (C₂ : NNReal)
    (hB : ∀ l ∈ inputLeaves LG.garden, 0 < (B l.1 : ℝ)) (hC₂ : 0 < (C₂ : ℝ)) :
    0 < leafSizeProduct LG (relativeLeafModificationCosts LG.garden S B C₂) := by
  classical
  apply prod_pos
  intro l hl
  let b : ActualInputLeaves LG.garden := ⟨l, hl⟩
  change 0 < (B b.1.1 : ℝ) * (leafModificationCosts LG.garden S 1 C₂ b.1.1 : ℝ)
  apply mul_pos (hB l hl)
  rw [leafModificationCosts_input]
  split_ifs
  · exact hC₂
  · norm_num

 theorem relative_combined_leaf_cost_product_le {w d m : ℕ} (LG : LayeredGarden w)
    (hp : LG.garden.IsPlain) (word : List (Fin d))
    (a : LeafDerivativeChoices LG.garden word.length) (c : RootWeightChoices LG.garden d m)
    (B : (Fin w × TTree.Path) → NNReal) (C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) :
    leafSizeProduct LG (relativeLeafModificationCosts LG.garden
      (combinedModifiedInputs LG.garden hp word a c) B C₂) ≤
      leafSizeProduct LG B * (C₂ : ℝ) ^ (2 * w * m + word.length) := by
  apply (relative_leaf_cost_product_le LG _ B C₂).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hC₂ (card_combinedModifiedInputs LG.garden hp word a c))
    (prod_nonneg (fun _ _ => NNReal.coe_nonneg _))

 theorem relative_combined_leaf_cost_sum_le {w d m : ℕ} (LG : LayeredGarden w)
    (hp : LG.garden.IsPlain) (word : List (Fin d))
    (B : (Fin w × TTree.Path) → NNReal) (C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) :
    (∑ a : LeafDerivativeChoices LG.garden word.length,
      ∑ c : RootWeightChoices LG.garden d m,
        ENNReal.ofReal (leafSizeProduct LG (relativeLeafModificationCosts LG.garden
          (combinedModifiedInputs LG.garden hp word a c) B C₂))) ≤
      (Fintype.card (LeafDerivativeChoices LG.garden word.length) : ℝ≥0∞) *
      (Fintype.card (RootWeightChoices LG.garden d m) : ℝ≥0∞) *
        ENNReal.ofReal (leafSizeProduct LG B * (C₂ : ℝ) ^ (2 * w * m + word.length)) := by
  classical
  have hh : (∑ a : LeafDerivativeChoices LG.garden word.length,
      ∑ c : RootWeightChoices LG.garden d m,
        ENNReal.ofReal (leafSizeProduct LG (relativeLeafModificationCosts LG.garden
          (combinedModifiedInputs LG.garden hp word a c) B C₂))) ≤
      ∑ _a : LeafDerivativeChoices LG.garden word.length,
        ∑ _c : RootWeightChoices LG.garden d m,
          ENNReal.ofReal (leafSizeProduct LG B * (C₂ : ℝ) ^ (2 * w * m + word.length)) := by
    apply sum_le_sum
    intro a _
    apply sum_le_sum
    intro c _
    exact ENNReal.ofReal_le_ofReal (relative_combined_leaf_cost_product_le LG hp word a c B C₂ hC₂)
  simpa only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, mul_assoc] using hh

end WaveTurbulence.LGSpine
