/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CombinedLeafControl
/-! Relative high-order leaf bounds preserve individual smallness factors after modifications. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def relativeLeafModificationCosts {w : ℕ} (G : Garden w)
    (S : Finset (ActualInputLeaves G)) (B : (Fin w × TTree.Path) → NNReal) (C₂ : NNReal) :
    (Fin w × TTree.Path) → NNReal := fun a => B a * leafModificationCosts G S 1 C₂ a

/-- The baseline bound may depend on the leaf. In particular, remainder leaves retain
L^(-theta) even when derivatives or root weights land on them. -/
theorem combined_leaf_profiles_controlled_relative {w d m : ℕ} (hd : 1 ≤ d)
    (LG : LayeredGarden w) (hp : LG.garden.IsPlain) (H : LeafProfiles w d)
    (word : List (Fin d)) (a : LeafDerivativeChoices LG.garden word.length)
    (c : RootWeightChoices LG.garden d m) (B : (Fin w × TTree.Path) → NNReal)
    (C₂ : NNReal) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * d + word.length : ℕ) (H l.1))
    (hlow : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * d) (40 * d) (H l.1) ≤ ENNReal.ofReal (B l.1 : ℝ))
    (hhigh : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * d + word.length) (40 * d + 4 * m) (H l.1) ≤ ENNReal.ofReal (C * B l.1))
    (hC₂ : (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m)) *
      ((d : ℝ) ^ (40 * d + word.length) * C) ≤ C₂) :
    LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c)
      (relativeLeafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) B C₂) := by
  classical
  intro l hl
  let b : ActualInputLeaves LG.garden := ⟨l, hl⟩
  change SNormR (40 * d) (40 * d)
      (rootModifiedProfiles LG.garden hp (leafDerivativeProfiles LG.garden H word a) c b.1.1) ≤
    ENNReal.ofReal ((B b.1.1 : ℝ) *
      (leafModificationCosts LG.garden (combinedModifiedInputs LG.garden hp word a c) 1 C₂ b.1.1 : ℝ))
  rw [leafModificationCosts_input]
  by_cases hb : b ∈ combinedModifiedInputs LG.garden hp word a c
  · rw [if_pos hb]
    apply (SNormR_combined_leaf_modification_bound hd LG.garden hp H word a c b
      (hc l hl) (C * B l.1) (mul_nonneg hC (NNReal.coe_nonneg _)) (hhigh l hl)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (B b.1.1 : ℝ) *
          (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m) *
            ((d : ℝ) ^ (40 * d + word.length) * C)) := by dsimp only [b]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC₂ (NNReal.coe_nonneg _)
  · rw [if_neg hb]
    have hr : b ∉ selectedInputs (rootCoordinateSlots LG.garden hp c) :=
      fun h => hb (mem_union_left _ h)
    have ha : b ∉ assignedDerivativeSupport LG.garden word a :=
      fun h => hb (mem_union_right _ h)
    rw [rootModifiedProfiles_eq_of_unselected LG.garden hp (leafDerivativeProfiles LG.garden H word a) c b hr,
      leafDerivativeProfiles_eq_of_unselected LG.garden H word a b ha]
    simpa only [NNReal.coe_one, mul_one] using hlow l hl

/-- The high-order multiplier is paid on the selected inputs only; the product of
all original baseline bounds, including a marked small remainder, remains intact. -/
theorem relative_leaf_cost_product_le {w : ℕ} (LG : LayeredGarden w)
    (S : Finset (ActualInputLeaves LG.garden)) (B : (Fin w × TTree.Path) → NNReal) (C₂ : NNReal) :
    leafSizeProduct LG (relativeLeafModificationCosts LG.garden S B C₂) ≤
      leafSizeProduct LG B * (C₂ : ℝ) ^ S.card := by
  have hh := leafModificationCosts_product_le LG S 1 C₂ (by norm_num)
  have hh' : leafSizeProduct LG (leafModificationCosts LG.garden S 1 C₂) ≤ (C₂ : ℝ) ^ S.card := by
    simpa only [NNReal.coe_one, one_pow, one_mul] using hh
  have he : leafSizeProduct LG (relativeLeafModificationCosts LG.garden S B C₂) =
      leafSizeProduct LG B * leafSizeProduct LG (leafModificationCosts LG.garden S 1 C₂) := by
    simp only [leafSizeProduct, relativeLeafModificationCosts, NNReal.coe_mul, prod_mul_distrib]
  rw [he]
  exact mul_le_mul_of_nonneg_left hh' (prod_nonneg (fun _ _ => NNReal.coe_nonneg _))

end WaveTurbulence.LGSpine
