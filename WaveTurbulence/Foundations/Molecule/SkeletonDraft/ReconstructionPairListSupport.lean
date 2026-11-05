/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListMembership
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CodeEndpointLeaves
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSubtrees

/-! # Every literal reconstruction pair endpoint is a leaf of the reconstructed forest -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.pairList_endpoints_valid {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (q : Pair w) (hq : q ∈ D.pairList hS) :
    q.1.2 ∈ (D.forest hS q.1.1).leaves ∧ q.2.2 ∈ (D.forest hS q.2.1).leaves := by
  rcases D.pairList_mem_cases hS q hq with ⟨p,hp⟩ | ⟨b,hb⟩
  · have hfirst := D.forest_subtree_position hS (p.firstLeaf hS).toNode
    rw [D.inflateNode_leaf,D.leafTree_first] at hfirst
    have hsecond := D.forest_subtree_position hS (p.secondLeaf hS).toNode
    rw [D.inflateNode_leaf,D.leafTree_second] at hsecond
    have hv := couple_pair_endpoint_leaves (D.couple p) _ _ q hp
    have hvalid (z : Address w)
        (hz : z ∈ leafAddresses (D.couple p).trees.1 (inflatedPosition S D.tree (p.firstLeaf hS).toNode) ∪
          leafAddresses (D.couple p).trees.2 (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) :
        z.2 ∈ (D.forest hS z.1).leaves := by
      rcases Finset.mem_union.mp hz with h | h
      · exact leafAddresses_subtree_valid (D.forest hS) _ _ hfirst z h
      · exact leafAddresses_subtree_valid (D.forest hS) _ _ hsecond z h
    exact ⟨hvalid q.1 hv.1,hvalid q.2 hv.2⟩
  · have hsub := D.forest_subtree_position hS b.toNode
    rw [D.inflateNode_branch] at hsub
    have hv := chain_pair_endpoint_leaves (D.tree b) (nodeSign S.sig b.1)
      (node3 (fun i => D.inflateNode hS (b.child i))) _ q hb
    exact ⟨leafAddresses_subtree_valid (D.forest hS) _ _ hsub q.1 hv.1,
      leafAddresses_subtree_valid (D.forest hS) _ _ hsub q.2 hv.2⟩

end WaveTurbulence.Reg.Skeleton
