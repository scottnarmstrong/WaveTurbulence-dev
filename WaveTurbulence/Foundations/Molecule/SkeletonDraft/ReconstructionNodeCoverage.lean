/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionInsertionBlocks

/-! # Every actual reconstructed node belongs to an insertion block -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.leaf_node_covered {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (ℓ : GLeaf S.tree) (target : Address w)
    (ht : target ∈ nodeAddresses (D.leafTree hS ℓ) (inflatedPosition S D.tree ℓ.toNode)) :
    ∃ slot : ReplacementSlot S, target ∈ D.nodeBlock hS slot := by
  obtain ⟨⟨p,i⟩,he⟩ := sourcePairLeaf_surjective S hS ℓ
  subst ℓ
  fin_cases i
  · change target ∈ nodeAddresses (D.leafTree hS (p.firstLeaf hS))
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode) at ht
    rw [D.leafTree_first hS p] at ht
    refine ⟨.inl p,?_⟩
    change target ∈ coupleNodes _ _ _
    rw [← couple_nodeAddresses]
    exact Finset.mem_union_left _ ht
  · change target ∈ nodeAddresses (D.leafTree hS (p.secondLeaf hS))
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode) at ht
    rw [D.leafTree_second hS p] at ht
    refine ⟨.inl p,?_⟩
    change target ∈ coupleNodes _ _ _
    rw [← couple_nodeAddresses]
    exact Finset.mem_union_right _ ht

theorem ReconstructionData.inflateNode_node_covered {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (a : GNode S.tree) (target : Address w)
    (ht : target ∈ nodeAddresses (D.inflateNode hS a) (inflatedPosition S D.tree a)) :
    ∃ slot : ReplacementSlot S, target ∈ D.nodeBlock hS slot := by
  cases hc : Comb.nodeSubtree a with
  | leaf =>
    let ℓ := leafOfSubtree a hc
    have ha : ℓ.toNode = a := rfl
    rw [← ha,D.inflateNode_leaf hS ℓ] at ht
    exact D.leaf_node_covered hS ℓ target ht
  | node l mid r =>
    let b := branchOfSubtree a l mid r hc
    have ha : b.toNode = a := rfl
    rw [← ha,D.inflateNode_branch hS b,chain_nodeAddresses] at ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact ⟨.inr b,Finset.mem_union_left _ ht⟩
    · have hnode : nodeAddresses (node3 (fun i => D.inflateNode hS (b.child i))) (D.corePosition b) =
          {D.corePosition b} ∪
          nodeAddresses (D.inflateNode hS (b.child 0)) (inflatedPosition S D.tree (b.child 0)) ∪
          nodeAddresses (D.inflateNode hS (b.child 1)) (inflatedPosition S D.tree (b.child 1)) ∪
          nodeAddresses (D.inflateNode hS (b.child 2)) (inflatedPosition S D.tree (b.child 2)) := by
        rw [node3,nodeAddresses_node,D.core_child_position,D.core_child_position,D.core_child_position]
      change target ∈ nodeAddresses _ (D.corePosition b) at ht
      rw [hnode] at ht
      rcases Finset.mem_union.mp ht with ht | ht
      · rcases Finset.mem_union.mp ht with ht | ht
        · rcases Finset.mem_union.mp ht with ht | ht
          · exact ⟨.inr b,Finset.mem_union_right _ ht⟩
          · exact D.inflateNode_node_covered hS (b.child 0) target ht
        · exact D.inflateNode_node_covered hS (b.child 1) target ht
      · exact D.inflateNode_node_covered hS (b.child 2) target ht
termination_by (Comb.nodeSubtree a).order
decreasing_by all_goals exact nodeSubtree_child_order_lt S.tree _ _

theorem ReconstructionData.node_covered {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS)) :
    ∃ slot : ReplacementSlot S, target.1 ∈ D.nodeBlock hS slot := by
  apply D.inflateNode_node_covered hS (GNode.root S.tree target.1.1) target.1
  rw [inflatedPosition_root]
  apply Finset.mem_image.mpr
  exact ⟨target.1.2,target.2,by simp only [addrExt,List.nil_append]⟩

end WaveTurbulence.Reg.Skeleton
