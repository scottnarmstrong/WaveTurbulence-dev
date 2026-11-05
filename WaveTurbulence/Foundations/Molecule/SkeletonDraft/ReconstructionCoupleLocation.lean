/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeLocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionSeparation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LeafIncomparability

/-! # Actual placement and node coverage of each coupled-leaf replacement -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.couple_frame_incomp {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    IncompAddr (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode) := by
  apply inflatedPosition_incomp
  have hn : p.secondLeaf hS ≠ p.firstLeaf hS := by
    intro he
    have hs := sourcePair_second_sign S hS p
    rw [he,sourcePair_first_sign] at hs
    exact (by decide : (1 : ℤˣ) ≠ -1) hs
  have hi := leaves_incomparable S.tree (p.firstLeaf hS) (p.secondLeaf hS) hn
  exact ⟨fun h => hi.1 ⟨h.1.symm,h.2⟩,fun h => hi.2 ⟨h.1.symm,h.2⟩⟩

theorem ReconstructionData.node_couple_location {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (p : SourcePair S) :
    target.1 ∈ coupleNodes (D.couple p)
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode) ∨
      (¬ Below (inflatedPosition S D.tree (p.firstLeaf hS).toNode) target.1 ∧
       ¬ Below (inflatedPosition S D.tree (p.secondLeaf hS).toNode) target.1) := by
  by_cases ha : Below (inflatedPosition S D.tree (p.firstLeaf hS).toNode) target.1
  · have ht := D.forest_subtree_position hS (p.firstLeaf hS).toNode
    rw [D.inflateNode_leaf hS,D.leafTree_first hS p] at ht
    have hn := node_mem_subtree_addresses (D.forest hS) _ target.1 _ ht target.2 ha
    exact Or.inl (by rw [← couple_nodeAddresses]; exact Finset.mem_union_left _ hn)
  by_cases hb : Below (inflatedPosition S D.tree (p.secondLeaf hS).toNode) target.1
  · have ht := D.forest_subtree_position hS (p.secondLeaf hS).toNode
    rw [D.inflateNode_leaf hS,D.leafTree_second hS p] at ht
    have hn := node_mem_subtree_addresses (D.forest hS) _ target.1 _ ht target.2 hb
    exact Or.inl (by rw [← couple_nodeAddresses]; exact Finset.mem_union_right _ hn)
  exact Or.inr ⟨ha,hb⟩

end WaveTurbulence.Reg.Skeleton
