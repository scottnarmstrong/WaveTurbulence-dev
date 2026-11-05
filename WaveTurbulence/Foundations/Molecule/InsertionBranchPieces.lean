/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistLeafExchange
public import WaveTurbulence.Foundations.Molecule.SpliceBranchSets

/-! # Actual branching-node transport for the subtree exchange

TARGET twist: the common forest's branching nodes are fixed and the
inserted crown's branching nodes move with their ordered subtrees.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (F : Fin w → TTree) (h : GLeaf F) (t : TTree)

/-- Exact branch addresses after insertion at a leaf; no old branch is removed. -/
theorem insertLeaf_branching : (insertLeaf F h t h.1.1).branching =
    (F h.1.1).branching ∪ t.branching.image (fun q => h.1.2 ++ q) := by
  rw [insertLeaf_at,Mole.branching_replaceAt_eq ((subtree_leaf_iff _ _).mpr h.2)]
  congr 1
  apply filter_eq_self.mpr
  intro q hq
  exact leaf_not_prefix_branch h.2 hq

/-- Branches in the common forest and in the inserted subtree. -/
abbrev InsertionBranchPiece := GBranch F ⊕ ↥t.branching

/-- Insert branching pieces at their actual new addresses. -/
@[expose] def insertionBranchMap : InsertionBranchPiece F t → GBranch (insertLeaf F h t)
  | .inl b => ⟨b.1,by
      by_cases hi : b.1.1 = h.1.1
      · rw [hi,insertLeaf_branching]
        exact mem_union_left _ (hi ▸ b.2)
      · rw [insertLeaf_other F h t _ hi]
        exact b.2⟩
  | .inr q => ⟨(h.1.1,h.1.2 ++ q.1),by
      rw [insertLeaf_branching]
      exact mem_union_right _ (mem_image.mpr ⟨q.1,q.2,rfl⟩)⟩

/-- The two branch pieces are disjoint and inject into the actual new forest. -/
theorem insertionBranchMap_injective : Function.Injective (insertionBranchMap F h t) := by
  rintro (b | q) (c | r) he
  · exact congrArg Sum.inl (Subtype.ext (congrArg (fun n : GBranch (insertLeaf F h t) => n.1) he))
  · have hi := congrArg (fun n : GBranch (insertLeaf F h t) => n.1.1) he
    have hp := congrArg (fun n : GBranch (insertLeaf F h t) => n.1.2) he
    exact (leaf_not_prefix_branch h.2 (hi ▸ b.2) ⟨r.1,hp.symm⟩).elim
  · have hi := congrArg (fun n : GBranch (insertLeaf F h t) => n.1.1) he
    have hp := congrArg (fun n : GBranch (insertLeaf F h t) => n.1.2) he
    exact (leaf_not_prefix_branch h.2 (hi.symm ▸ c.2) ⟨q.1,hp⟩).elim
  · have hp := congrArg (fun n : GBranch (insertLeaf F h t) => n.1.2) he
    exact congrArg Sum.inr (Subtype.ext (List.append_cancel_left hp))

/-- Every actual new branch belongs to a branch piece. -/
theorem insertionBranchMap_surjective : Function.Surjective (insertionBranchMap F h t) := by
  intro b
  by_cases hi : b.1.1 = h.1.1
  · have hm : b.1.2 ∈ (insertLeaf F h t h.1.1).branching := hi ▸ b.2
    rw [insertLeaf_branching] at hm
    rcases mem_union.mp hm with hm | hm
    · exact ⟨.inl ⟨b.1,hi.symm ▸ hm⟩,Subtype.ext rfl⟩
    · obtain ⟨q,hq,hpath⟩ := mem_image.mp hm
      exact ⟨.inr ⟨q,hq⟩,Subtype.ext (Prod.ext hi.symm hpath)⟩
  · refine ⟨.inl ⟨b.1,?_⟩,Subtype.ext rfl⟩
    have hb := b.2
    rw [insertLeaf_other F h t _ hi] at hb
    exact hb

/-- The actual branching-node insertion bijection. -/
@[expose] noncomputable def insertionBranchEquiv : InsertionBranchPiece F t ≃ GBranch (insertLeaf F h t) :=
  Equiv.ofBijective (insertionBranchMap F h t)
    ⟨insertionBranchMap_injective F h t,insertionBranchMap_surjective F h t⟩

/-- Branching-node bijection for the concrete lower-subtree exchange. -/
@[expose] noncomputable def exchangeBranchEquiv (h₁ : GLeaf F) (keep : Fin 3) :
    GBranch (insertLeaf F h t) ≃ GBranch (insertLeaf F h₁ (switchFree keep t)) :=
  (insertionBranchEquiv F h t).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (switchBranchEquiv keep t)).trans
      (insertionBranchEquiv F h₁ (switchFree keep t)))

end WaveTurbulence.Twist
