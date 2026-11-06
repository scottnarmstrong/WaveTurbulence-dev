/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBShape
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BarePairInnerReplacement

/-! # Actual extraction and node guards for inserting and erasing bare chain contexts -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.insertChain_subtree {w : ℕ} (R : Raw w) (a : Address w) (X : RegChain)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    Comb.subtree ((R.insertChain a X).tree a.1) a.2 =
      some (X.plug (nodeSign R.sig a) ((R.tree a.1).subtreeAt a.2)) := by
  let A : GNode R.tree := ⟨a,ha⟩
  change Comb.subtree (Function.update R.tree a.1
    ((R.tree a.1).setAt a.2 (X.plug (nodeSign R.sig a) ((R.tree a.1).subtreeAt a.2))) a.1) a.2 = _
  rw [Function.update_self,setAt_eq_replaceAt]
  exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec A) _

theorem Raw.opB_continuing_node {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) :
    (addrExt a [m.c]).2 ∈ ((R.opB a m).tree (addrExt a [m.c]).1).nodes := by
  apply (Comb.subtree_exists_iff _ _).mp
  refine ⟨node3 (fun j => if j = m.lone then (R.tree a.1).subtreeAt a.2 else .leaf),?_⟩
  change Comb.subtree ((R.opB a m).tree a.1) (a.2 ++ [m.c]) = _
  rw [Comb.subtree_append,R.opB_subtree a m ha]
  exact miniContext_subtree_continuing m _

theorem Raw.insertChain_pair_rest_node {w : ℕ} (R : Raw w) (a : Address w)
    (ha : a.2 ∈ (R.tree a.1).nodes) (m : MiniTreeCode) (X : RegChain) :
    (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])).2 ∈
      ((R.insertChain a (.pair m .triv .triv X .nil)).tree
        (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])).1).nodes := by
  apply (Comb.subtree_exists_iff _ _).mp
  refine ⟨(R.tree a.1).subtreeAt a.2,?_⟩
  change Comb.subtree ((R.insertChain a (.pair m .triv .triv X .nil)).tree a.1)
    (a.2 ++ ([m.c] ++ X.lonePath ++ [m.lone])) = _
  rw [Comb.subtree_append,R.insertChain_subtree a _ ha]
  exact bare_pair_subtree_rest m X _ _

end WaveTurbulence.Reg.Skeleton
