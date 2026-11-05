/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleRootSubtrees
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden

/-! # A literal root pair can remain in a replacement's matching only for the trivial code -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.couple_eq_triv_of_root_pair_mem {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S)
    (hp : (inflatedPosition S D.tree (p.firstLeaf hS).toNode,
      inflatedPosition S D.tree (p.secondLeaf hS).toNode) ∈ (D.raw hS).pairs) : D.couple p = .triv := by
  have hv := (D.raw_valid hS).1 _ hp
  have hfirst : (D.couple p).trees.1 = .leaf := Option.some.inj
    ((D.forest_subtree_pair_first hS p).symm.trans (Comb.subtree_of_mem_leaves hv.1))
  have hsecond : (D.couple p).trees.2 = .leaf := Option.some.inj
    ((D.forest_subtree_pair_second hS p).symm.trans (Comb.subtree_of_mem_leaves hv.2.1))
  have hz : (D.couple p).size = 0 := (code_trees_order (D.couple p)).symm.trans (by
    rw [hfirst,hsecond]
    rfl)
  exact eq_triv_of_wf_size_zero (D.couple p) (D.couple_wf p) hz

end WaveTurbulence.Reg.Skeleton
