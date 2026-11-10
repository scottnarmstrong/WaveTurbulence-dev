/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! FLOWER-P7: the disjoint union of two forests along an index equivalence `σ : Fin a ⊕ Fin b ≃ Fin w`.
The glued forest has `T (σ (inl i)) = TA i` and `T (σ (inr i)) = TB i`.  This file gives the equivalences of
nodes, leaves and branching nodes: `GNode TA ⊕ GNode TB ≃ GNode (gT σ TA TB)` and likewise for leaves and
branching nodes (one generic equivalence over a predicate `S : TTree → Finset Path`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

/-- The glued forest. -/
def gT (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) : Fin w → TTree :=
  fun c => Sum.elim TA TB (σ.symm c)

@[simp] theorem gT_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (i : Fin a) :
    gT σ TA TB (σ (.inl i)) = TA i := by simp [gT]

@[simp] theorem gT_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (i : Fin b) :
    gT σ TA TB (σ (.inr i)) = TB i := by simp [gT]

/-- Generic sub-forest sets: addresses `(j, p)` with `p ∈ S (T j)`. -/
abbrev SubSet {n : ℕ} (T : Fin n → TTree) (S : TTree → Finset Path) : Type :=
  {x : Fin n × Path // x.2 ∈ S (T x.1)}

/-- The map of `glueSub`. -/
def glueSubMap (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) (S : TTree → Finset Path) :
    SubSet TA S ⊕ SubSet TB S → SubSet (gT σ TA TB) S
  | .inl x => ⟨(σ (.inl x.1.1), x.1.2), by simpa using x.2⟩
  | .inr x => ⟨(σ (.inr x.1.1), x.1.2), by simpa using x.2⟩

theorem glueSubMap_bijective (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (S : TTree → Finset Path) : Function.Bijective (glueSubMap σ TA TB S) := by
  constructor
  · rintro (x | x) (y | y) h
    all_goals
      have h' := congrArg Subtype.val h
      simp only [glueSubMap, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq] at h'
    all_goals first
      | exact h'.1.elim
      | exact congrArg Sum.inl (Subtype.ext (Prod.ext h'.1 h'.2))
      | exact congrArg Sum.inr (Subtype.ext (Prod.ext h'.1 h'.2))
  · rintro ⟨⟨c, p⟩, hp⟩
    obtain ⟨s, rfl⟩ := σ.surjective c
    rcases s with i | i
    · exact ⟨.inl ⟨(i, p), by simpa using hp⟩, rfl⟩
    · exact ⟨.inr ⟨(i, p), by simpa using hp⟩, rfl⟩

/-- Generic equivalence for nodes, leaves, branching nodes of the glued forest. -/
noncomputable def glueSub (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (S : TTree → Finset Path) : SubSet TA S ⊕ SubSet TB S ≃ SubSet (gT σ TA TB) S :=
  Equiv.ofBijective _ (glueSubMap_bijective σ TA TB S)

noncomputable def glueNode (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) :
    GNode TA ⊕ GNode TB ≃ GNode (gT σ TA TB) := glueSub σ TA TB TTree.nodes

noncomputable def glueLeaf (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) :
    GLeaf TA ⊕ GLeaf TB ≃ GLeaf (gT σ TA TB) := glueSub σ TA TB TTree.leaves

noncomputable def glueBranch (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree) :
    GBranch TA ⊕ GBranch TB ≃ GBranch (gT σ TA TB) := glueSub σ TA TB TTree.branching

@[simp] theorem glueNode_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TA) : (glueNode σ TA TB (.inl x)).1 = (σ (.inl x.1.1), x.1.2) := rfl
@[simp] theorem glueNode_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GNode TB) : (glueNode σ TA TB (.inr x)).1 = (σ (.inr x.1.1), x.1.2) := rfl
@[simp] theorem glueLeaf_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GLeaf TA) : (glueLeaf σ TA TB (.inl x)).1 = (σ (.inl x.1.1), x.1.2) := rfl
@[simp] theorem glueLeaf_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GLeaf TB) : (glueLeaf σ TA TB (.inr x)).1 = (σ (.inr x.1.1), x.1.2) := rfl
@[simp] theorem glueBranch_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TA) : (glueBranch σ TA TB (.inl x)).1 = (σ (.inl x.1.1), x.1.2) := rfl
@[simp] theorem glueBranch_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TB) : (glueBranch σ TA TB (.inr x)).1 = (σ (.inr x.1.1), x.1.2) := rfl

/-- `toNode` is compatible with gluing. -/
theorem glueBranch_toNode_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TA) : (glueBranch σ TA TB (.inl x)).toNode = glueNode σ TA TB (.inl x.toNode) := rfl
theorem glueBranch_toNode_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TB) : (glueBranch σ TA TB (.inr x)).toNode = glueNode σ TA TB (.inr x.toNode) := rfl
theorem glueLeaf_toNode_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GLeaf TA) : (glueLeaf σ TA TB (.inl x)).toNode = glueNode σ TA TB (.inl x.toNode) := rfl
theorem glueLeaf_toNode_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GLeaf TB) : (glueLeaf σ TA TB (.inr x)).toNode = glueNode σ TA TB (.inr x.toNode) := rfl

theorem glueBranch_child_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TA) (i : Fin 3) :
    (glueBranch σ TA TB (.inl x)).child i = glueNode σ TA TB (.inl (x.child i)) := by
  apply Subtype.ext
  rfl
theorem glueBranch_child_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x : GBranch TB) (i : Fin 3) :
    (glueBranch σ TA TB (.inr x)).child i = glueNode σ TA TB (.inr (x.child i)) := by
  apply Subtype.ext
  rfl

end WaveTurbulence.FlowerP7
