/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueSurj
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.EmbSum
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapAttach
/-! FLOWER-P7: the conditions of the canonical families on a glued layered garden are the conditions on
the two parts: plainness, the canonicity criterion, attachment orders, top orders. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem glue_isPlain_iff (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) :
    (glueGarden σ GA GB).IsPlain ↔ GA.IsPlain ∧ GB.IsPlain := by
  unfold Garden.IsPlain
  constructor
  · intro h
    exact ⟨fun ℓ => by simpa [glue_mark_leaf_inl] using h (glueLeaf σ GA.tree GB.tree (.inl ℓ)),
      fun ℓ => by simpa [glue_mark_leaf_inr] using h (glueLeaf σ GA.tree GB.tree (.inr ℓ))⟩
  · rintro ⟨hA, hB⟩ ℓ
    obtain ⟨y, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
    rcases y with y | y
    · rw [glue_mark_leaf_inl]; exact hA y
    · rw [glue_mark_leaf_inr]; exact hB y

/-! ### Descendant structure -/

theorem glue_isDesc_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (x x' : GNode TA) :
    (glueNode σ TA TB (.inl x)).IsDesc (glueNode σ TA TB (.inl x')) ↔ x.IsDesc x' := by
  unfold GNode.IsDesc
  simp [glueNode_inl]

theorem glue_isDesc_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (x x' : GNode TB) :
    (glueNode σ TA TB (.inr x)).IsDesc (glueNode σ TA TB (.inr x')) ↔ x.IsDesc x' := by
  unfold GNode.IsDesc
  simp [glueNode_inr]

theorem not_glue_isDesc_inl_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TA) (x' : GNode TB) :
    ¬ (glueNode σ TA TB (.inl x)).IsDesc (glueNode σ TA TB (.inr x')) := by
  rintro ⟨h, -⟩
  simp [glueNode_inl, glueNode_inr] at h

theorem not_glue_isDesc_inr_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TB) (x' : GNode TA) :
    ¬ (glueNode σ TA TB (.inr x)).IsDesc (glueNode σ TA TB (.inl x')) := by
  rintro ⟨h, -⟩
  simp [glueNode_inl, glueNode_inr] at h

/-! ### Top orders -/

theorem glue_topOrder_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b) (p : ℕ)
    (i : Fin a) : (glueLayered σ LA LB).topOrder p (σ (.inl i)) = LA.topOrder p i := by
  classical
  unfold LayeredGarden.topOrder
  have : (Finset.univ.filter fun br : GBranch (glueLayered σ LA LB).garden.tree =>
      br.1.1 = σ (.inl i) ∧ (glueLayered σ LA LB).layer br.toNode = p) =
      (Finset.univ.filter fun br : GBranch LA.garden.tree => br.1.1 = i ∧ LA.layer br.toNode = p).image
        (fun x => glueBranch σ LA.garden.tree LB.garden.tree (.inl x)) := by
    ext br
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective br
      rcases y with y | y
      · refine ⟨y, ⟨?_, ?_⟩, rfl⟩
        · simpa using h1
        · rwa [gLayer_branch_inl] at h2
      · exfalso
        simp [glueBranch_inr] at h1
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨by simp [h1], ?_⟩
      rwa [gLayer_branch_inl]
  rw [this, Finset.card_image_of_injective _ (fun x y h =>
    Sum.inl_injective ((glueBranch σ LA.garden.tree LB.garden.tree).injective h))]

theorem glue_topOrder_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b) (p : ℕ)
    (i : Fin b) : (glueLayered σ LA LB).topOrder p (σ (.inr i)) = LB.topOrder p i := by
  classical
  unfold LayeredGarden.topOrder
  have : (Finset.univ.filter fun br : GBranch (glueLayered σ LA LB).garden.tree =>
      br.1.1 = σ (.inr i) ∧ (glueLayered σ LA LB).layer br.toNode = p) =
      (Finset.univ.filter fun br : GBranch LB.garden.tree => br.1.1 = i ∧ LB.layer br.toNode = p).image
        (fun x => glueBranch σ LA.garden.tree LB.garden.tree (.inr x)) := by
    ext br
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective br
      rcases y with y | y
      · exfalso
        simp [glueBranch_inl] at h1
      · refine ⟨y, ⟨?_, ?_⟩, rfl⟩
        · simpa using h1
        · rwa [gLayer_branch_inr] at h2
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨by simp [h1], ?_⟩
      rwa [gLayer_branch_inr]
  rw [this, Finset.card_image_of_injective _ (fun x y h =>
    Sum.inr_injective ((glueBranch σ LA.garden.tree LB.garden.tree).injective h))]

end WaveTurbulence.FlowerP7
