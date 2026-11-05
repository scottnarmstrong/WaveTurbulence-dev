/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots

/-! # Two exact decompositions of a sum over actual forest nodes -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Leaves and branching nodes form the exact disjoint partition of actual nodes. -/
noncomputable def nodeKindEquiv {w : ℕ} (tree : Fin w → TTree) : GLeaf tree ⊕ GBranch tree ≃ GNode tree :=
  Equiv.ofBijective (Sum.elim GLeaf.toNode GBranch.toNode) ⟨by
    intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : GNode tree => z.1) he))
      | inr y =>
        have hv := congrArg Subtype.val he
        exact (Comb.TreePath.not_mem_branching_of_mem_leaves _ x.2 (hv ▸ y.2)).elim
    | inr x =>
      cases y with
      | inl y =>
        have hv := congrArg Subtype.val he
        exact (Comb.TreePath.not_mem_branching_of_mem_leaves _ y.2 (hv ▸ x.2)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : GNode tree => z.1) he)),by
    intro a
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with hl | hb
    · exact ⟨.inl ⟨a.1,hl⟩,Subtype.ext rfl⟩
    · exact ⟨.inr ⟨a.1,hb⟩,Subtype.ext rfl⟩⟩

theorem sum_nodes_leaf_branch {w : ℕ} (tree : Fin w → TTree) (f : GNode tree → ℕ) :
    (∑ a, f a) = (∑ ℓ : GLeaf tree, f ℓ.toNode) + ∑ b : GBranch tree, f b.toNode := by
  rw [← (nodeKindEquiv tree).sum_comp f,Fintype.sum_sum_type]
  rfl

theorem sum_nodes_root_child {w : ℕ} (tree : Fin w → TTree) (f : GNode tree → ℕ) :
    (∑ a, f a) = (∑ j, f (GNode.root tree j)) + ∑ b : GBranch tree, ∑ i : Fin 3, f (b.child i) := by
  rw [← (nodeSlotEquiv tree).symm.sum_comp f,Fintype.sum_sum_type,Fintype.sum_prod_type]
  rfl

end WaveTurbulence.Reg.Skeleton
