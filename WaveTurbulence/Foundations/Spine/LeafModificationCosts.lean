/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SelectedInputCount
public import WaveTurbulence.Foundations.Spine.RootModifiedProfileNorm
public import WaveTurbulence.Foundations.Spine.LeafDerivativeSupport
/-! Individual input costs for the union of coordinate-weight and derivative modifications. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def leafModificationCosts {w : ℕ} (G : Garden w)
    (bad : Finset (ActualInputLeaves G)) (C₁ C₂ : NNReal) : (Fin w × TTree.Path) → NNReal := by
  classical
  exact fun x => if x ∈ bad.image (inputRawAddress G) then C₂ else C₁

theorem leafModificationCosts_input {w : ℕ} (G : Garden w) (bad : Finset (ActualInputLeaves G))
    (C₁ C₂ : NNReal) (l : ActualInputLeaves G) :
    leafModificationCosts G bad C₁ C₂ l.1.1 = if l ∈ bad then C₂ else C₁ := by
  classical
  have he : inputRawAddress G l ∈ bad.image (inputRawAddress G) ↔ l ∈ bad := by
    constructor
    · intro hm
      obtain ⟨r, hr, heq⟩ := mem_image.mp hm
      exact (inputRawAddress_injective G heq) ▸ hr
    · intro hm
      exact mem_image.mpr ⟨l, hm, rfl⟩
  unfold leafModificationCosts
  change (if inputRawAddress G l ∈ _ then C₂ else C₁) = _
  simp only [he]

theorem leafModificationCosts_product_le {w : ℕ} (LG : LayeredGarden w)
    (bad : Finset (ActualInputLeaves LG.garden)) (C₁ C₂ : NNReal) (hC₁ : (1 : ℝ) ≤ C₁) :
    leafSizeProduct LG (leafModificationCosts LG.garden bad C₁ C₂) ≤
      (C₁ : ℝ) ^ (inputLeaves LG.garden).card * (C₂ : ℝ) ^ bad.card := by
  classical
  have hb := leaf_cost_product_le (univ : Finset (ActualInputLeaves LG.garden)) bad
    (subset_univ _) (fun l => leafModificationCosts LG.garden bad C₁ C₂ l.1.1)
    (C₁ : ℝ) (C₂ : ℝ) (fun l _ => by
      rw [leafModificationCosts_input]
      by_cases hl : l ∈ bad
      · simp only [hl, ite_true]
        exact le_mul_of_one_le_left (NNReal.coe_nonneg C₂) hC₁
      · simp only [hl, ite_false, mul_one, le_refl])
  have he : leafSizeProduct LG (leafModificationCosts LG.garden bad C₁ C₂) =
      ∏ l : ActualInputLeaves LG.garden, (leafModificationCosts LG.garden bad C₁ C₂ l.1.1 : ℝ) := by
    unfold leafSizeProduct
    exact (prod_coe_sort (inputLeaves LG.garden)
      (fun l : GLeaf LG.garden.tree => (leafModificationCosts LG.garden bad C₁ C₂ l.1 : ℝ))).symm
  rw [he]
  simpa only [card_univ, Fintype.card_coe] using hb

noncomputable def combinedModifiedInputs {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (word : List (Fin d)) (a : LeafDerivativeChoices G word.length) (c : RootWeightChoices G d m) :
    Finset (ActualInputLeaves G) := by
  classical
  exact selectedInputs (rootCoordinateSlots G hp c) ∪ assignedDerivativeSupport G word a

theorem card_combinedModifiedInputs {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (word : List (Fin d)) (a : LeafDerivativeChoices G word.length) (c : RootWeightChoices G d m) :
    (combinedModifiedInputs G hp word a c).card ≤ 2 * w * m + word.length :=
  (card_union_le _ _).trans (Nat.add_le_add (card_root_modified_inputs G hp c)
    (card_assignedDerivativeSupport G word a))

end WaveTurbulence.LGSpine
