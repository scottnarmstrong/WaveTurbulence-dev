/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueGarden
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! FLOWER-P7: the glue of two layered gardens, and the splitting of order, sign, `ζ`, `ε`, `Ω`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem glueGarden_tree (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) :
    (glueGarden σ GA GB).tree = gT σ GA.tree GB.tree := rfl

/-- The glued layering. -/
noncomputable def gLayer (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) : GNode (glueGarden σ GA GB).tree → ℕ :=
  fun x => Sum.elim lA lB ((glueNode σ GA.tree GB.tree).symm x)

@[simp] theorem gLayer_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (x : GNode GA.tree) :
    gLayer σ GA GB lA lB (glueNode σ GA.tree GB.tree (.inl x)) = lA x := by
  simp [gLayer]

@[simp] theorem gLayer_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (x : GNode GB.tree) :
    gLayer σ GA GB lA lB (glueNode σ GA.tree GB.tree (.inr x)) = lB x := by
  simp [gLayer]

theorem glue_pair_leaf_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GLeaf GA.tree) :
    (glueGarden σ GA GB).pair (glueLeaf σ GA.tree GB.tree (.inl x)) =
      glueLeaf σ GA.tree GB.tree (.inl (GA.pair x)) := by
  simp [glueGarden]

theorem glue_pair_leaf_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GLeaf GB.tree) :
    (glueGarden σ GA GB).pair (glueLeaf σ GA.tree GB.tree (.inr x)) =
      glueLeaf σ GA.tree GB.tree (.inr (GB.pair x)) := by
  simp [glueGarden]

theorem glue_mark_leaf_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GLeaf GA.tree) :
    (glueGarden σ GA GB).mark (glueLeaf σ GA.tree GB.tree (.inl x)) = GA.mark x := by
  simp [glueGarden]

theorem glue_mark_leaf_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GLeaf GB.tree) :
    (glueGarden σ GA GB).mark (glueLeaf σ GA.tree GB.tree (.inr x)) = GB.mark x := by
  simp [glueGarden]

theorem gLayer_isLayering (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    {lA : GNode GA.tree → ℕ} {lB : GNode GB.tree → ℕ} (hA : IsLayering GA lA) (hB : IsLayering GB lB) :
    IsLayering (glueGarden σ GA GB) (gLayer σ GA GB lA lB) := by
  constructor
  · intro br i
    obtain ⟨y, rfl⟩ := (glueBranch σ GA.tree GB.tree).surjective br
    rcases y with y | y
    · rw [glueBranch_child_inl, glueBranch_toNode_inl, gLayer_inl, gLayer_inl]
      exact hA.1 y i
    · rw [glueBranch_child_inr, glueBranch_toNode_inr, gLayer_inr, gLayer_inr]
      exact hB.1 y i
  · intro ℓ
    obtain ⟨y, rfl⟩ := (glueLeaf σ GA.tree GB.tree).surjective ℓ
    rcases y with y | y
    · rw [glue_pair_leaf_inl, glueLeaf_toNode_inl, glueLeaf_toNode_inl, gLayer_inl, gLayer_inl]
      exact hA.2 y
    · rw [glue_pair_leaf_inr, glueLeaf_toNode_inr, glueLeaf_toNode_inr, gLayer_inr, gLayer_inr]
      exact hB.2 y

/-- The glue of two layered gardens. -/
@[reducible] noncomputable def glueLayered (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b) :
    LayeredGarden w where
  garden := glueGarden σ LA.garden LB.garden
  layer := gLayer σ LA.garden LB.garden LA.layer LB.layer
  isLayering := gLayer_isLayering σ LA.garden LB.garden LA.isLayering LB.isLayering

theorem glueLayered_layer_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GNode LA.garden.tree) :
    (glueLayered σ LA LB).layer (glueNode σ LA.garden.tree LB.garden.tree (.inl x)) = LA.layer x :=
  gLayer_inl ..

theorem glueLayered_layer_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GNode LB.garden.tree) :
    (glueLayered σ LA LB).layer (glueNode σ LA.garden.tree LB.garden.tree (.inr x)) = LB.layer x :=
  gLayer_inr ..

/-! ### Order and `ζ` -/

theorem glue_order (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) :
    (glueGarden σ GA GB).order = GA.order + GB.order := by
  unfold Garden.order
  rw [← σ.sum_comp, Fintype.sum_sum_type]
  simp [glueGarden]

/-- The sign of a glued node. -/
theorem glue_sign_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GNode GA.tree) :
    (glueGarden σ GA GB).sign (glueNode σ GA.tree GB.tree (.inl x)) = GA.sign x := by
  show nodeSign (gSig σ GA.sig GB.sig) (σ (.inl x.1.1), x.1.2) = nodeSign GA.sig x.1
  exact nodeSign_glue_inl σ GA.sig GB.sig x.1

theorem glue_sign_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (x : GNode GB.tree) :
    (glueGarden σ GA GB).sign (glueNode σ GA.tree GB.tree (.inr x)) = GB.sign x := by
  show nodeSign (gSig σ GA.sig GB.sig) (σ (.inr x.1.1), x.1.2) = nodeSign GB.sig x.1
  exact nodeSign_glue_inr σ GA.sig GB.sig x.1

theorem glue_zeta (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) :
    (glueGarden σ GA GB).zeta = GA.zeta * GB.zeta := by
  unfold Garden.zeta
  rw [← (glueBranch σ GA.tree GB.tree).prod_comp, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [glueBranch_toNode_inl, glue_sign_inl]
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [glueBranch_toNode_inr, glue_sign_inr]

end WaveTurbulence.FlowerP7
