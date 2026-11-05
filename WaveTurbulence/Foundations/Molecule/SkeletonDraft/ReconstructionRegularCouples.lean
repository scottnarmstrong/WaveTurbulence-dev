/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubcoupleCodeDecoding
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns
public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # Every literal couple replacement is an actual source-regular embedded couple -/

public section
namespace WaveTurbulence.Reg.Skeleton

 theorem ReconstructionData.decodedNode_sign {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (a : GNode S.tree) : G.sign (D.decodedNode hS hd a) = nodeSign S.sig a.1 := by
  have hs := congrArg Raw.sig hd.2
  change S.sig = G.sig at hs
  change nodeSign G.sig (inflatedPosition S D.tree a) = _
  rw [← hs]
  exact inflatedPosition_sign S D.tree a

 theorem ReconstructionData.decoded_couple_decodes {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (p : SourcePair S) : (D.couple p).Decodes
      (Comb.subCoupleGarden (D.decoded_couple_isSubCouple hS hd p)) := by
  apply subCoupleGarden_decodes_of_block
  · exact (D.decodedNode_sign hS hd _).trans (sourcePair_first_sign S hS p)
  · exact (D.decoded_subtree_position hS hd (p.firstLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_first hS p)))
  · exact (D.decoded_subtree_position hS hd (p.secondLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_second hS p)))
  · exact D.couple_pair_mem hS hd p

 theorem ReconstructionData.decoded_couple_regular {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (p : SourcePair S) : IsRegularCouple
      (Comb.subCoupleGarden (D.decoded_couple_isSubCouple hS hd p)) :=
  (isRegularCouple_iff_exists_wf_decodes _).mpr
    ⟨D.couple p,D.couple_wf p,D.decoded_couple_decodes hS hd p⟩

end WaveTurbulence.Reg.Skeleton
