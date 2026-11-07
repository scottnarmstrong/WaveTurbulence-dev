/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueCanon
/-! FLOWER-P7: attachment nodes and attached orders of a glued layered garden. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem orderBelow_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TA) : (glueNode σ TA TB (.inl x)).orderBelow = x.orderBelow := by
  classical
  unfold GNode.orderBelow
  have : (Finset.univ.filter fun br : GBranch (gT σ TA TB) => (glueNode σ TA TB (.inl x)).IsDesc br.toNode) =
      (Finset.univ.filter fun br : GBranch TA => x.IsDesc br.toNode).image
        (fun y => glueBranch σ TA TB (.inl y)) := by
    ext br
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨z, rfl⟩ := (glueBranch σ TA TB).surjective br
      rcases z with y | y
      · exact ⟨y, by rwa [glueBranch_toNode_inl, glue_isDesc_inl] at h, rfl⟩
      · exfalso; rw [glueBranch_toNode_inr] at h; exact not_glue_isDesc_inl_inr σ TA TB x y.toNode h
    · rintro ⟨y, h, rfl⟩
      rwa [glueBranch_toNode_inl, glue_isDesc_inl]
  rw [this, Finset.card_image_of_injective _ (fun u v h => Sum.inl_injective ((glueBranch σ TA TB).injective h))]

theorem mem_attachNodes_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (x : GNode LA.garden.tree) :
    glueNode σ LA.garden.tree LB.garden.tree (.inl x) ∈ (glueLayered σ LA LB).attachNodes p ↔
      x ∈ LA.attachNodes p := by
  rw [mem_attachNodes_iff, mem_attachNodes_iff, glueLayered_layer_inl, parentLayer_glue_inl]

theorem orderBelow_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TB) : (glueNode σ TA TB (.inr x)).orderBelow = x.orderBelow := by
  classical
  unfold GNode.orderBelow
  have : (Finset.univ.filter fun br : GBranch (gT σ TA TB) => (glueNode σ TA TB (.inr x)).IsDesc br.toNode) =
      (Finset.univ.filter fun br : GBranch TB => x.IsDesc br.toNode).image
        (fun y => glueBranch σ TA TB (.inr y)) := by
    ext br
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨z, rfl⟩ := (glueBranch σ TA TB).surjective br
      rcases z with y | y
      · exfalso; rw [glueBranch_toNode_inl] at h; exact not_glue_isDesc_inr_inl σ TA TB x y.toNode h
      · exact ⟨y, by rwa [glueBranch_toNode_inr, glue_isDesc_inr] at h, rfl⟩
    · rintro ⟨y, h, rfl⟩
      rwa [glueBranch_toNode_inr, glue_isDesc_inr]
  rw [this, Finset.card_image_of_injective _ (fun u v h => Sum.inr_injective ((glueBranch σ TA TB).injective h))]

theorem mem_attachNodes_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (x : GNode LB.garden.tree) :
    glueNode σ LA.garden.tree LB.garden.tree (.inr x) ∈ (glueLayered σ LA LB).attachNodes p ↔
      x ∈ LB.attachNodes p := by
  rw [mem_attachNodes_iff, mem_attachNodes_iff, glueLayered_layer_inr, parentLayer_glue_inr]


theorem attachLinked_glue_inl_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GNode LA.garden.tree) (y : GNode LB.garden.tree) :
    ¬ (glueLayered σ LA LB).AttachLinked (glueNode σ LA.garden.tree LB.garden.tree (.inl x))
      (glueNode σ LA.garden.tree LB.garden.tree (.inr y)) := by
  rintro ⟨ℓ, hℓ, hp⟩
  rw [mem_leavesBelow_glue_inl] at hℓ
  obtain ⟨ℓ0, _, rfl⟩ := hℓ
  rw [mem_leavesBelow_glue_inr] at hp
  obtain ⟨ℓ1, _, e⟩ := hp
  have e' := glue_pair_leaf_inl σ LA.garden LB.garden ℓ0
  have e2 : glueLeaf σ LA.garden.tree LB.garden.tree (.inr ℓ1) =
      glueLeaf σ LA.garden.tree LB.garden.tree (.inl (LA.garden.pair ℓ0)) := e.trans e'
  have := (glueLeaf σ LA.garden.tree LB.garden.tree).injective e2
  simp at this

theorem attachLinked_glue_inr_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GNode LB.garden.tree) (y : GNode LA.garden.tree) :
    ¬ (glueLayered σ LA LB).AttachLinked (glueNode σ LA.garden.tree LB.garden.tree (.inr x))
      (glueNode σ LA.garden.tree LB.garden.tree (.inl y)) := by
  rintro ⟨ℓ, hℓ, hp⟩
  rw [mem_leavesBelow_glue_inr] at hℓ
  obtain ⟨ℓ0, _, rfl⟩ := hℓ
  rw [mem_leavesBelow_glue_inl] at hp
  obtain ⟨ℓ1, _, e⟩ := hp
  have e' := glue_pair_leaf_inr σ LA.garden LB.garden ℓ0
  have e2 : glueLeaf σ LA.garden.tree LB.garden.tree (.inl ℓ1) =
      glueLeaf σ LA.garden.tree LB.garden.tree (.inr (LB.garden.pair ℓ0)) := e.trans e'
  have := (glueLeaf σ LA.garden.tree LB.garden.tree).injective e2
  simp at this

theorem attachLinked_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x y : GNode LA.garden.tree) :
    (glueLayered σ LA LB).AttachLinked (glueNode σ LA.garden.tree LB.garden.tree (.inl x))
      (glueNode σ LA.garden.tree LB.garden.tree (.inl y)) ↔ LA.AttachLinked x y := by
  unfold LayeredGarden.AttachLinked
  simp only [mem_leavesBelow_glue_inl]
  constructor
  · rintro ⟨ℓ, ⟨ℓ0, h0, rfl⟩, ℓ1, h1, e⟩
    have e' := glue_pair_leaf_inl σ LA.garden LB.garden ℓ0
    have e2 : glueLeaf σ LA.garden.tree LB.garden.tree (.inl ℓ1) =
        glueLeaf σ LA.garden.tree LB.garden.tree (.inl (LA.garden.pair ℓ0)) := e.trans e'
    have := Sum.inl_injective ((glueLeaf σ LA.garden.tree LB.garden.tree).injective e2)
    subst this
    exact ⟨ℓ0, h0, h1⟩
  · rintro ⟨ℓ, h0, h1⟩
    refine ⟨glueLeaf σ LA.garden.tree LB.garden.tree (.inl ℓ), ⟨ℓ, h0, rfl⟩, LA.garden.pair ℓ, h1, ?_⟩
    exact (glue_pair_leaf_inl _ _ _ _).symm

theorem attachLinked_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x y : GNode LB.garden.tree) :
    (glueLayered σ LA LB).AttachLinked (glueNode σ LA.garden.tree LB.garden.tree (.inr x))
      (glueNode σ LA.garden.tree LB.garden.tree (.inr y)) ↔ LB.AttachLinked x y := by
  unfold LayeredGarden.AttachLinked
  simp only [mem_leavesBelow_glue_inr]
  constructor
  · rintro ⟨ℓ, ⟨ℓ0, h0, rfl⟩, ℓ1, h1, e⟩
    have e' := glue_pair_leaf_inr σ LA.garden LB.garden ℓ0
    have e2 : glueLeaf σ LA.garden.tree LB.garden.tree (.inr ℓ1) =
        glueLeaf σ LA.garden.tree LB.garden.tree (.inr (LB.garden.pair ℓ0)) := e.trans e'
    have := Sum.inr_injective ((glueLeaf σ LA.garden.tree LB.garden.tree).injective e2)
    subst this
    exact ⟨ℓ0, h0, h1⟩
  · rintro ⟨ℓ, h0, h1⟩
    refine ⟨glueLeaf σ LA.garden.tree LB.garden.tree (.inr ℓ), ⟨ℓ, h0, rfl⟩, LB.garden.pair ℓ, h1, ?_⟩
    exact (glue_pair_leaf_inr _ _ _ _).symm

theorem attachedOrder_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (u : GNode LA.garden.tree) :
    (glueLayered σ LA LB).attachedOrder p (glueNode σ LA.garden.tree LB.garden.tree (.inl u)) =
      LA.attachedOrder p u := by
  classical
  unfold LayeredGarden.attachedOrder
  refine sum_filter_eqvGen_embedding (fun x => glueNode σ LA.garden.tree LB.garden.tree (.inl x))
    (fun x y h => Sum.inl_injective ((glueNode σ LA.garden.tree LB.garden.tree).injective h)) _ _
    (fun x => mem_attachNodes_glue_inl σ LA LB p x) _ _ (fun x y => ?_) (fun x y h => ?_) _ _
    (fun x => orderBelow_glue_inl σ _ _ x) u
  · unfold LayeredGarden.AttachLinkedOn
    rw [mem_attachNodes_glue_inl, mem_attachNodes_glue_inl, attachLinked_glue_inl]
  · unfold LayeredGarden.AttachLinkedOn at h
    obtain ⟨-, -, hl⟩ := h
    obtain ⟨zx, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x
    obtain ⟨zy, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective y
    rcases zx with zx | zx <;> rcases zy with zy | zy
    · exact ⟨fun _ => ⟨zy, rfl⟩, fun _ => ⟨zx, rfl⟩⟩
    · exact absurd hl (attachLinked_glue_inl_inr σ LA LB zx zy)
    · exact absurd hl (attachLinked_glue_inr_inl σ LA LB zx zy)
    · refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨z, hz⟩ => ?_⟩ <;>
        exact absurd ((glueNode σ LA.garden.tree LB.garden.tree).injective hz) (by simp)

theorem attachedOrder_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) (u : GNode LB.garden.tree) :
    (glueLayered σ LA LB).attachedOrder p (glueNode σ LA.garden.tree LB.garden.tree (.inr u)) =
      LB.attachedOrder p u := by
  classical
  unfold LayeredGarden.attachedOrder
  refine sum_filter_eqvGen_embedding (fun x => glueNode σ LA.garden.tree LB.garden.tree (.inr x))
    (fun x y h => Sum.inr_injective ((glueNode σ LA.garden.tree LB.garden.tree).injective h)) _ _
    (fun x => mem_attachNodes_glue_inr σ LA LB p x) _ _ (fun x y => ?_) (fun x y h => ?_) _ _
    (fun x => orderBelow_glue_inr σ _ _ x) u
  · unfold LayeredGarden.AttachLinkedOn
    rw [mem_attachNodes_glue_inr, mem_attachNodes_glue_inr, attachLinked_glue_inr]
  · unfold LayeredGarden.AttachLinkedOn at h
    obtain ⟨-, -, hl⟩ := h
    obtain ⟨zx, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x
    obtain ⟨zy, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective y
    rcases zx with zx | zx <;> rcases zy with zy | zy
    · refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨z, hz⟩ => ?_⟩ <;>
        exact absurd ((glueNode σ LA.garden.tree LB.garden.tree).injective hz) (by simp)
    · exact absurd hl (attachLinked_glue_inl_inr σ LA LB zx zy)
    · exact absurd hl (attachLinked_glue_inr_inl σ LA LB zx zy)
    · exact ⟨fun _ => ⟨zy, rfl⟩, fun _ => ⟨zx, rfl⟩⟩

/-- The attachment condition of a glued garden. -/
theorem glue_attach_cond (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p M : ℕ) :
    (∀ u ∈ (glueLayered σ LA LB).attachNodes p, (glueLayered σ LA LB).attachedOrder p u ≤ M) ↔
      (∀ u ∈ LA.attachNodes p, LA.attachedOrder p u ≤ M) ∧ (∀ u ∈ LB.attachNodes p, LB.attachedOrder p u ≤ M) := by
  constructor
  · intro h
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · have := h (glueNode σ LA.garden.tree LB.garden.tree (.inl u)) ((mem_attachNodes_glue_inl σ LA LB p u).2 hu)
      rwa [attachedOrder_glue_inl] at this
    · have := h (glueNode σ LA.garden.tree LB.garden.tree (.inr u)) ((mem_attachNodes_glue_inr σ LA LB p u).2 hu)
      rwa [attachedOrder_glue_inr] at this
  · rintro ⟨hA, hB⟩ x hx
    obtain ⟨y, rfl⟩ := (glueNode σ LA.garden.tree LB.garden.tree).surjective x
    rcases y with y | y
    · rw [attachedOrder_glue_inl]; exact hA y ((mem_attachNodes_glue_inl σ LA LB p y).1 hx)
    · rw [attachedOrder_glue_inr]; exact hB y ((mem_attachNodes_glue_inr σ LA LB p y).1 hx)

end WaveTurbulence.FlowerP7


