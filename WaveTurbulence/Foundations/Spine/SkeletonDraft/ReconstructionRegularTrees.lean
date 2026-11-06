/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionChainBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionRegularCouples
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubPairedTreeCodeDecoding

/-! # Every branch replacement is an actual source-regular embedded paired tree -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.decoded_chain_decodes {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : (D.tree b).DecodesTree
      (Comb.embeddedPairedTree (D.decoded_chain_isSubPairedTree hS hd b)) := by
  apply embeddedPairedTree_decodes_of_block (D.tree b) G
    (D.decodedNode hS hd b.toNode) (D.decodedCoreNode hS hd b)
    (D.decoded_chain_isSubPairedTree hS hd b) (node3 (fun i => D.inflateNode hS (b.child i)))
  · have hs := D.decodedNode_sign hS hd b.toNode
    rw [hs]
    exact (D.decoded_subtree_position hS hd b.toNode).trans
      (congrArg some (D.inflateNode_branch hS b))
  · rfl
  · have hs := D.decodedNode_sign hS hd b.toNode
    rw [hs]
    exact D.chain_pair_mem hS hd b

theorem ReconstructionData.decoded_chain_regular {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : IsRegularTree
      (Comb.embeddedPairedTree (D.decoded_chain_isSubPairedTree hS hd b)) :=
  (isRegularTree_iff_exists_wf_decodesTree _).mpr
    ⟨D.tree b,D.tree_wf b,D.decoded_chain_decodes hS hd b⟩

end WaveTurbulence.Reg.Skeleton
