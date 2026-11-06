/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SelectedInputCount
public import WaveTurbulence.Foundations.Spine.RootModifiedProfileNorm
public import WaveTurbulence.Foundations.Spine.LeafCostProduct
/-! Only the selected leaves pay the high-order input constant in the producer estimates. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def rootModifiedCosts {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (C₁ C₂ : NNReal) : (Fin w × TTree.Path) → NNReal := by
  classical
  exact fun a => if a ∈ (selectedInputs (rootCoordinateSlots G hp c)).image (inputRawAddress G)
    then C₂ else C₁

theorem rootModifiedCosts_input {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (C₁ C₂ : NNReal) (l : ActualInputLeaves G) :
    rootModifiedCosts G hp c C₁ C₂ l.1.1 =
      if l ∈ selectedInputs (rootCoordinateSlots G hp c) then C₂ else C₁ := by
  classical
  have he : inputRawAddress G l ∈
      (selectedInputs (rootCoordinateSlots G hp c)).image (inputRawAddress G) ↔
      l ∈ selectedInputs (rootCoordinateSlots G hp c) :=
    by
      constructor
      · intro hm
        obtain ⟨r, hr, heq⟩ := mem_image.mp hm
        exact (inputRawAddress_injective G heq) ▸ hr
      · intro hm
        exact mem_image.mpr ⟨l, hm, rfl⟩
  unfold rootModifiedCosts
  change (if inputRawAddress G l ∈ _ then C₂ else C₁) = _
  simp only [he]

theorem rootModifiedCosts_product_le {w d m : ℕ} (LG : LayeredGarden w)
    (hp : LG.garden.IsPlain) (c : RootWeightChoices LG.garden d m)
    (C₁ C₂ : NNReal) (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂) :
    leafSizeProduct LG (rootModifiedCosts LG.garden hp c C₁ C₂) ≤
      (C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ (2 * w * m) := by
  classical
  let G := LG.garden
  let bad := selectedInputs (rootCoordinateSlots G hp c)
  have hb := leaf_cost_product_le (univ : Finset (ActualInputLeaves G)) bad
    (subset_univ _) (fun l => rootModifiedCosts G hp c C₁ C₂ l.1.1)
    (C₁ : ℝ) (C₂ : ℝ) (fun l _ => by
      rw [rootModifiedCosts_input]
      by_cases hl : l ∈ selectedInputs (rootCoordinateSlots G hp c)
      · simp only [bad, hl, ite_true]
        exact le_mul_of_one_le_left (NNReal.coe_nonneg C₂) hC₁
      · simp only [bad, hl, ite_false, mul_one, le_refl])
  have he : leafSizeProduct LG (rootModifiedCosts G hp c C₁ C₂) =
      ∏ l : ActualInputLeaves G, (rootModifiedCosts G hp c C₁ C₂ l.1.1 : ℝ) := by
    unfold leafSizeProduct
    exact (prod_coe_sort (inputLeaves G)
      (fun l : GLeaf G.tree => (rootModifiedCosts G hp c C₁ C₂ l.1 : ℝ))).symm
  rw [he]
  apply hb.trans
  simp only [card_univ, Fintype.card_coe]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hC₂ (card_root_modified_inputs G hp c)) (pow_nonneg (NNReal.coe_nonneg C₁) _)

/-- The actual root-weight modifications meet the literal individual-input premises of
REGREF/PL234, with low cost on every input not selected by the finite weight choices. -/
theorem rootModifiedProfiles_controlled {w d m : ℕ} (hd : 1 ≤ d)
    (LG : LayeredGarden w) (hp : LG.garden.IsPlain) (H : LeafProfiles w d)
    (c : RootWeightChoices LG.garden d m) (C₁ C₂ : NNReal) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * d) (fun x => (H l.1 x : ℂ)))
    (hlow : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * d) (40 * d) (H l.1) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * d) (40 * d + 4 * m) (H l.1) ≤
      ENNReal.ofReal C)
    (hC₂ : (((2 : ℝ) ^ (40 * d) * (d : ℝ) ^ (40 * d)) ^ (4 * m)) * C ≤ C₂) :
    LeafwiseControlled LG (rootModifiedProfiles LG.garden hp H c)
      (rootModifiedCosts LG.garden hp c C₁ C₂) := by
  classical
  intro l hl
  let a : ActualInputLeaves LG.garden := ⟨l, hl⟩
  have hcost := rootModifiedCosts_input LG.garden hp c C₁ C₂ a
  change SNormR (40 * d) (40 * d) (rootModifiedProfiles LG.garden hp H c a.1.1) ≤
    ENNReal.ofReal (rootModifiedCosts LG.garden hp c C₁ C₂ a.1.1 : ℝ)
  rw [hcost]
  by_cases ha : a ∈ selectedInputs (rootCoordinateSlots LG.garden hp c)
  · rw [if_pos ha]
    exact (SNormR_rootModifiedProfile_bound hd LG.garden hp H c a (hc l hl) C hC
      (hhigh l hl)).trans (ENNReal.ofReal_le_ofReal hC₂)
  · rw [if_neg ha, rootModifiedProfiles_eq_of_unselected LG.garden hp H c a ha]
    exact hlow l hl

end WaveTurbulence.LGSpine
