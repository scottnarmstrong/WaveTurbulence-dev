/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CombinedLeafCostSum
/-! Uniform numerical leaf-cost budgets for all derivatives in a fixed spatial seminorm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem combined_leaf_cost_sum_uniform {w d m A : ℕ} (LG : LayeredGarden w) (hp : LG.garden.IsPlain)
    (word : List (Fin d)) (hw : word.length ≤ A)
    (C₁ C₂ : NNReal) (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂) :
    (∑ a : LeafDerivativeChoices LG.garden word.length,
      ∑ c : RootWeightChoices LG.garden d m,
        ENNReal.ofReal (leafSizeProduct LG
          (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) C₁ C₂))) ≤
      (((inputLeaves LG.garden).card + 1 : ℕ) : ℝ≥0∞) ^ A *
      (Fintype.card (RootWeightChoices LG.garden d m) : ℝ≥0∞) *
      ENNReal.ofReal ((C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (2 * w * m + A)) := by
  apply (combined_leaf_cost_sum_le LG hp word C₁ C₂ hC₁ hC₂).trans
  have hcard : Fintype.card (LeafDerivativeChoices LG.garden word.length) ≤
      ((inputLeaves LG.garden).card + 1) ^ A := by
    rw [card_leafDerivativeChoices]
    exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (by omega) hw)
  have hcard' : (Fintype.card (LeafDerivativeChoices LG.garden word.length) : ℝ≥0∞) ≤
      (((inputLeaves LG.garden).card + 1 : ℕ) : ℝ≥0∞) ^ A := by exact_mod_cast hcard
  apply mul_le_mul
  · exact mul_le_mul hcard' le_rfl (by positivity) (by positivity)
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC₂ (Nat.add_le_add_left hw _))
      (pow_nonneg (NNReal.coe_nonneg _) _)

  · positivity
  · positivity

end WaveTurbulence.LGSpine
