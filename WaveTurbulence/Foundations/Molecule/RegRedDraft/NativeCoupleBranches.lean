/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.ReplacementBranchPartition
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestBranches
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple

/-! # Native regular-couple coordinates inside the actual reconstructed garden -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def attachedNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (a : GNode S.tree) : GNode (D.forest hS) :=
  ⟨inflatedPosition S D.tree a,(Comb.subtree_exists_iff _ _).mp ⟨_,D.forest_subtree_position hS a⟩⟩

noncomputable def nativeCoupleForest {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : Comb.RootedSubforest (D.forest hS) 2 where
  root := ![attachedNode D hS (p.firstLeaf hS).toNode,attachedNode D hS (p.secondLeaf hS).toNode]
  shape := (decodedCouple (D.couple p)).tree
  subtree_eq := by
    intro j
    fin_cases j
    · exact (D.forest_subtree_position hS (p.firstLeaf hS).toNode).trans
        (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_first hS p)))
    · exact (D.forest_subtree_position hS (p.secondLeaf hS).toNode).trans
        (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_second hS p)))
  incomparable := by
    have hi := D.couple_frame_incomp hS p
    have hpair : (attachedNode D hS (p.firstLeaf hS).toNode).Incomparable
        (attachedNode D hS (p.secondLeaf hS).toNode) :=
      ⟨fun h => hi.1 ⟨h.1.symm,h.2⟩,fun h => hi.2 ⟨h.1.symm,h.2⟩⟩
    intro i j hn
    fin_cases i <;> fin_cases j
    · exact (hn rfl).elim
    · exact hpair
    · exact ⟨hpair.2,hpair.1⟩
    · exact (hn rfl).elim

noncomputable def coupleContextBranch {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) :
    GBranch (decodedCouple (D.couple p)).tree ↪ GBranch (D.forest hS) :=
  subforestBranchEmbedding (nativeCoupleForest D hS p)

theorem coupleContextBranch_mem_block {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) (b : GBranch (decodedCouple (D.couple p)).tree) :
    (coupleContextBranch D hS p b).1 ∈ D.nodeBlock hS (.inl p) := by
  change (coupleContextBranch D hS p b).1 ∈ coupleNodes (D.couple p)
    (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
    (inflatedPosition S D.tree (p.secondLeaf hS).toNode)
  rw [← couple_nodeAddresses]
  obtain ⟨⟨j,q⟩,hq⟩ := b
  fin_cases j
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨q,TTree.branching_subset_nodes _ hq,rfl⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q,TTree.branching_subset_nodes _ hq,rfl⟩

end WaveTurbulence.RegRed
