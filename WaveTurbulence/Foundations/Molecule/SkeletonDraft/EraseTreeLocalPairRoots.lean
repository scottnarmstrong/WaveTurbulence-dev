/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeDescendantPosition
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchLocalNaturality
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds

/-! # Exact local transport at source slots that cannot contain the erased branch -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem leaf_not_above_branch {w : ℕ} (tree : Fin w → TTree)
    (ℓ : GLeaf tree) (b : GBranch tree) : ¬ Below ℓ.1 b.1 := by
  intro h
  have hb : b.1.2 ∈ (tree ℓ.1.1).branching := h.1 ▸ b.2
  have hp := leaf_prefix_node_eq ℓ.2 (TTree.branching_subset_nodes _ hb) h.2
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _ ℓ.2 (hp.symm ▸ hb)

theorem ReconstructionData.eraseTree_pair_root_transport {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b : GBranch S.tree) (a : GNode S.tree)
    (ha : ¬ Below a.1 b.1) :
    let A := inflatedPosition S (D.eraseTree b).tree b.toNode
    inflatedPosition S D.tree a = stretch A (D.tree b).lonePath
      (inflatedPosition S (D.eraseTree b).tree a) ∧
    RespectsAt (stretch A (D.tree b).lonePath) (inflatedPosition S (D.eraseTree b).tree a) := by
  dsimp only
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  by_cases hb : Below b.1 a.1
  · have hn : a ≠ b.toNode := by
      intro he
      apply ha
      exact he ▸ ⟨rfl,List.prefix_refl _⟩
    exact ⟨D.eraseTree_position_descendant b a hb hn,
      stretch_respectsAt_below A _ _ (inflatedPosition_below S E.tree b.toNode a hb)⟩
  · have hi := inflatedPosition_incomp S E.tree b.toNode a ⟨hb,ha⟩
    refine ⟨?_,stretch_respectsAt_incomp A _ _ hi⟩
    exact (D.eraseTree_position_of_not_below b a hb).symm.trans
      (stretch_outside A (D.tree b).lonePath _ hi.1).symm

end WaveTurbulence.Reg.Skeleton
