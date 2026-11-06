/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafModificationCosts
public import WaveTurbulence.Foundations.Spine.CombinedLeafModificationNorm
/-! The exact weighted derivative profiles meet the published leafwise source estimates
with a high-order cost only on the explicitly selected input leaves. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem combined_leaf_profiles_controlled {w d m : ℕ} (hd : 1 ≤ d)
    (LG : LayeredGarden w) (hp : LG.garden.IsPlain) (H : LeafProfiles w d)
    (word : List (Fin d)) (a : LeafDerivativeChoices LG.garden word.length)
    (c : RootWeightChoices LG.garden d m) (C₁ C₂ : NNReal) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * d + word.length : ℕ) (H l.1))
    (hlow : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * d) (40 * d) (H l.1) ≤ ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * d + word.length) (40 * d + 4 * m) (H l.1) ≤ ENNReal.ofReal C)
    (hC₂ : (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m)) *
      ((d : ℝ) ^ (40 * d + word.length) * C) ≤ C₂) :
    LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c)
      (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) C₁ C₂) := by
  classical
  intro l hl
  let b : ActualInputLeaves LG.garden := ⟨l, hl⟩
  change SNormR (40 * d) (40 * d)
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c b.1.1) ≤
    ENNReal.ofReal (leafModificationCosts LG.garden
      (combinedModifiedInputs LG.garden hp word a c) C₁ C₂ b.1.1 : ℝ)
  rw [leafModificationCosts_input]
  by_cases hb : b ∈ combinedModifiedInputs LG.garden hp word a c
  · rw [if_pos hb]
    exact (SNormR_combined_leaf_modification_bound hd LG.garden hp H word a c b
      (hc l hl) C hC (hhigh l hl)).trans (ENNReal.ofReal_le_ofReal hC₂)
  · rw [if_neg hb]
    have hr : b ∉ selectedInputs (rootCoordinateSlots LG.garden hp c) :=
      fun h => hb (mem_union_left _ h)
    have ha : b ∉ assignedDerivativeSupport LG.garden word a :=
      fun h => hb (mem_union_right _ h)
    rw [rootModifiedProfiles_eq_of_unselected LG.garden hp (leafDerivativeProfiles LG.garden H word a) c b hr,
      leafDerivativeProfiles_eq_of_unselected LG.garden H word a b ha]
    exact hlow l hl

theorem combined_leaf_cost_product_le {w d m : ℕ} (LG : LayeredGarden w) (hp : LG.garden.IsPlain)
    (word : List (Fin d)) (a : LeafDerivativeChoices LG.garden word.length)
    (c : RootWeightChoices LG.garden d m) (C₁ C₂ : NNReal) (hC₁ : (1 : ℝ) ≤ C₁)
    (hC₂ : (1 : ℝ) ≤ C₂) :
    leafSizeProduct LG
      (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) C₁ C₂) ≤
      (C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (2 * w * m + word.length) := by
  apply (leafModificationCosts_product_le LG _ C₁ C₂ hC₁).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hC₂ (card_combinedModifiedInputs LG.garden hp word a c))
    (pow_nonneg (NNReal.coe_nonneg C₁) _)

end WaveTurbulence.LGSpine
