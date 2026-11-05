/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionChainBlocks
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.ReplaceTree

/-! # Exact C4 embedded attachments supplied by actual reconstruction data -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

private theorem pair_eq_of_source_first {w : ℕ} (G : Garden w) (q : Pair w)
    (hq : q ∈ sourcePairs G) (l : GLeaf G.tree) (hl : l.1 = q.1) : (G.pair l).1 = q.2 := by
  obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hq
  have hml : m = l := Subtype.ext ((congrArg Prod.fst he).trans hl.symm)
  subst m
  exact congrArg Prod.snd he

/-- Every native regular-tree attachment is a literal C4 embedded chain. -/
theorem reconstruction_chainEmb {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (b : GBranch S.tree) :
    ChainEmb G (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)
      (node3 (fun i => D.inflateNode hS (b.child i))) where
  node := (D.decodedNode hS hd b.toNode).2
  tree := subtreeAt_eq_of_subtree _ _ _
    ((D.decoded_subtree_position hS hd b.toNode).trans (congrArg some (D.inflateNode_branch hS b)))
  pairs := fun q hq l hl => pair_eq_of_source_first G q (D.chain_pair_mem hS hd b q hq) l hl

/-- Every native regular-couple attachment is a literal C4 embedded couple. -/
theorem reconstruction_coupleEmb {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (p : SourcePair S) :
    Embeds G (D.couple p) (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode) where
  indep := Comb.subCouple_incomparable (D.decoded_couple_isSubCouple hS hd p)
  nodeA := (D.decodedNode hS hd (p.firstLeaf hS).toNode).2
  nodeB := (D.decodedNode hS hd (p.secondLeaf hS).toNode).2
  treeA := subtreeAt_eq_of_subtree _ _ _
    ((D.decoded_subtree_position hS hd (p.firstLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_first hS p))))
  treeB := subtreeAt_eq_of_subtree _ _ _
    ((D.decoded_subtree_position hS hd (p.secondLeaf hS).toNode).trans
      (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_second hS p))))
  pairs := fun q hq l hl => pair_eq_of_source_first G q (D.couple_pair_mem hS hd p q hq) l hl

end WaveTurbulence.LFTwist
