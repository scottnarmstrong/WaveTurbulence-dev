/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafProfileSelection
public import WaveTurbulence.Foundations.Spine.MarkedLeafProduct
/-! Selected leaf profiles preserve individual seminorm bounds and a marked remainder gain. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset
open scoped Classical

noncomputable def selectLeafBounds {w : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal) : (Fin w × TTree.Path) → NNReal := fun a =>
  if a ∈ S.image (fun l => l.1) then B₁ a else B₀ a

 theorem selectLeafBounds_apply {w : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal) (l : GLeaf G.tree) :
    selectLeafBounds G S B₀ B₁ l.1 = if l ∈ S then B₁ l.1 else B₀ l.1 := by
  have hm : l.1 ∈ S.image (fun l => l.1) ↔ l ∈ S := by
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := mem_image.mp h
      exact (Subtype.ext he : a = l) ▸ ha
    · exact fun h => mem_image.mpr ⟨l, h, rfl⟩
  simp only [selectLeafBounds, hm]

 theorem LeafwiseControlled.select {w d : ℕ} (LG : LayeredGarden w)
    (S : Finset (GLeaf LG.garden.tree)) (H₀ H₁ : LeafProfiles w d)
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal)
    (h₀ : LeafwiseControlled LG H₀ B₀) (h₁ : LeafwiseControlled LG H₁ B₁) :
    LeafwiseControlled LG (selectLeafProfiles LG.garden S H₀ H₁)
      (selectLeafBounds LG.garden S B₀ B₁) := by
  intro l hl
  by_cases hs : l ∈ S
  · have he : selectLeafProfiles LG.garden S H₀ H₁ l.1 = H₁ l.1 := by
      funext x
      simp only [selectLeafProfiles_apply, ite_eq_left hs]
    rw [he, selectLeafBounds_apply, ite_eq_left hs]
    exact h₁ l hl
  · have he : selectLeafProfiles LG.garden S H₀ H₁ l.1 = H₀ l.1 := by
      funext x
      simp only [selectLeafProfiles_apply, ite_eq_right hs]
    rw [he, selectLeafBounds_apply, ite_eq_right hs]
    exact h₀ l hl

/-- Every nonempty remainder subset carries one actual small factor in the source product. -/
theorem selected_leaf_product_le_marked {w : ℕ} (G : Garden w) (S : Finset (GLeaf G.tree))
    (hSI : S ⊆ inputLeaves G) (hne : S.Nonempty)
    (B₀ B₁ : (Fin w × TTree.Path) → NNReal) (ε : NNReal)
    (hB : ∀ l ∈ inputLeaves G, B₁ l.1 ≤ B₀ l.1)
    (hsmall : ∀ l ∈ S, B₁ l.1 ≤ ε * B₀ l.1) :
    (∏ l ∈ inputLeaves G, selectLeafBounds G S B₀ B₁ l.1) ≤
      ε * ∏ l ∈ inputLeaves G, B₀ l.1 := by
  apply prod_le_marked_factor
  · intro l hl
    rw [selectLeafBounds_apply]
    split_ifs
    · exact hB l hl
    · rfl
  · obtain ⟨l, hl⟩ := hne
    refine ⟨l, hSI hl, ?_⟩
    rw [selectLeafBounds_apply, ite_eq_left hl]
    exact hsmall l hl

end WaveTurbulence.LGSpine
