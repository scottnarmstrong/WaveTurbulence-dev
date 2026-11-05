/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSubtrees

/-! # Actual embedded couple blocks in a literal decoded reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton

 theorem ReconstructionData.decoded_subtree_position {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (a : GNode S.tree) :
    Comb.subtree (G.tree (inflatedPosition S D.tree a).1)
      (inflatedPosition S D.tree a).2 = some (D.inflateNode hS a) := by
  have ht := congrArg Raw.tree hd.2
  change D.forest hS = G.tree at ht
  rw [← ht]
  exact D.forest_subtree_position hS a

/-- The actual target node at an original source node's inflated position. -/
@[expose] noncomputable def ReconstructionData.decodedNode {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (a : GNode S.tree) : GNode G.tree :=
  ⟨inflatedPosition S D.tree a,
    (Comb.subtree_exists_iff _ _).mp ⟨_,D.decoded_subtree_position hS hd a⟩⟩

 theorem ReconstructionData.couple_pair_mem {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (p : SourcePair S) (q : Pair w)
    (hq : q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) : q ∈ sourcePairs G := by
  have hp := congrArg Raw.pairs hd.2
  change D.attachmentPairs hS = sourcePairs G at hp
  rw [← hp]
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  exact ⟨p,Finset.mem_univ _,List.mem_toFinset.mpr hq⟩

 theorem ReconstructionData.decoded_couple_isSubCouple {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (p : SourcePair S) : Comb.IsSubCouple G
      (D.decodedNode hS hd (p.firstLeaf hS).toNode)
      (D.decodedNode hS hd (p.secondLeaf hS).toNode) := by
  apply subCouple_of_source_block (D.couple p) G hd.1
  · exact (D.decoded_subtree_position hS hd (p.firstLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_first hS p)))
  · exact (D.decoded_subtree_position hS hd (p.secondLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_second hS p)))
  · exact D.couple_pair_mem hS hd p

end WaveTurbulence.Reg.Skeleton
