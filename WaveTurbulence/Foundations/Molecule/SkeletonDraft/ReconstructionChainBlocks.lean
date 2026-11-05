/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceChainBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # Each branch replacement is an actual embedded paired-tree interval -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.decoded_subtree_core {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : Comb.subtree (G.tree (D.corePosition b).1) (D.corePosition b).2 =
      some (node3 (fun i => D.inflateNode hS (b.child i))) := by
  have ht := congrArg Raw.tree hd.2
  change D.forest hS = G.tree at ht
  rw [← ht]
  exact D.forest_subtree_core hS b

/-- The lower boundary of a tree replacement is its actual surviving source branch. -/
noncomputable def ReconstructionData.decodedCoreNode {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : GNode G.tree :=
  ⟨D.corePosition b,(Comb.subtree_exists_iff _ _).mp ⟨_,D.decoded_subtree_core hS hd b⟩⟩

theorem ReconstructionData.chain_pair_mem {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) (q : Pair w)
    (hq : q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) :
    q ∈ sourcePairs G := by
  have hp := congrArg Raw.pairs hd.2
  change D.attachmentPairs hS = sourcePairs G at hp
  rw [← hp]
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,List.mem_toFinset.mpr hq⟩

theorem ReconstructionData.decoded_chain_isSubPairedTree {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : Comb.IsSubPairedTree G
      (D.decodedNode hS hd b.toNode) (D.decodedCoreNode hS hd b) := by
  apply subPairedTree_of_source_block (D.tree b) (nodeSign S.sig b.1) G hd.1
    (D.decodedNode hS hd b.toNode) (D.decodedCoreNode hS hd b)
    (node3 (fun i => D.inflateNode hS (b.child i)))
  · exact (D.decoded_subtree_position hS hd b.toNode).trans
      (congrArg some (D.inflateNode_branch hS b))
  · exact D.decoded_subtree_core hS hd b
  · rfl
  · exact D.chain_pair_mem hS hd b

end WaveTurbulence.Reg.Skeleton
