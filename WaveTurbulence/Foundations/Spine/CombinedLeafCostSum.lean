/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CombinedLeafControl
/-! Explicit finite cost sums in weighted derivative estimates. The high norm cost is paid
only by the bounded number of modified original inputs. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem combined_leaf_cost_sum_le {w d m : ℕ} (LG : LayeredGarden w) (hp : LG.garden.IsPlain)
    (word : List (Fin d)) (C₁ C₂ : NNReal) (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂) :
    (∑ a : LeafDerivativeChoices LG.garden word.length,
      ∑ c : RootWeightChoices LG.garden d m,
        ENNReal.ofReal (leafSizeProduct LG
          (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) C₁ C₂))) ≤
      (Fintype.card (LeafDerivativeChoices LG.garden word.length) : ℝ≥0∞) *
      (Fintype.card (RootWeightChoices LG.garden d m) : ℝ≥0∞) *
      ENNReal.ofReal ((C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (2 * w * m + word.length)) := by
  classical
  have h : (∑ a : LeafDerivativeChoices LG.garden word.length,
      ∑ c : RootWeightChoices LG.garden d m,
        ENNReal.ofReal (leafSizeProduct LG
          (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) C₁ C₂))) ≤
      ∑ _a : LeafDerivativeChoices LG.garden word.length,
        ∑ _c : RootWeightChoices LG.garden d m,
          ENNReal.ofReal ((C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (2 * w * m + word.length)) := by
    apply sum_le_sum
    intro a _
    apply sum_le_sum
    intro c _
    exact ENNReal.ofReal_le_ofReal (combined_leaf_cost_product_le LG hp word a c C₁ C₂ hC₁ hC₂)
  simpa only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, mul_assoc] using h

end WaveTurbulence.LGSpine
