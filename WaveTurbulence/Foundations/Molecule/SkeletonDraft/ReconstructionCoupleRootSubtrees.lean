/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListSupport

/-! # Exact ordered subtree shapes at every shared couple replacement's two source roots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.forest_subtree_pair_first {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    Comb.subtree (D.forest hS (inflatedPosition S D.tree (p.firstLeaf hS).toNode).1)
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode).2 = some (D.couple p).trees.1 :=
  (D.forest_subtree_position hS (p.firstLeaf hS).toNode).trans
    (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_first hS p)))

theorem ReconstructionData.forest_subtree_pair_second {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    Comb.subtree (D.forest hS (inflatedPosition S D.tree (p.secondLeaf hS).toNode).1)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode).2 = some (D.couple p).trees.2 :=
  (D.forest_subtree_position hS (p.secondLeaf hS).toNode).trans
    (congrArg some ((D.inflateNode_leaf hS _).trans (D.leafTree_second hS p)))

end WaveTurbulence.Reg.Skeleton
