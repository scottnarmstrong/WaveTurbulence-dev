/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeLocalPairRoots
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ListPairImages

/-! # Exact transport of every leaf-pair replacement block under one tree-slot erasure -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_couple_pair_block {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) (p : SourcePair S) :
    let E := D.eraseTree b
    let A := inflatedPosition S E.tree b.toNode
    ((D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)).toFinset =
    (((E.couple p).pairsAt (inflatedPosition S E.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S E.tree (p.secondLeaf hS).toNode)).toFinset.image
        (fun q => (stretch A (D.tree b).lonePath q.1,stretch A (D.tree b).lonePath q.2))) := by
  classical
  dsimp only
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hl := D.eraseTree_pair_root_transport b (p.firstLeaf hS).toNode
    (leaf_not_above_branch S.tree (p.firstLeaf hS) b)
  have hr := D.eraseTree_pair_root_transport b (p.secondLeaf hS).toNode
    (leaf_not_above_branch S.tree (p.secondLeaf hS) b)
  have he := couple_pairsAt_map_local (D.couple p) (stretch A (D.tree b).lonePath) _ _ hl.2 hr.2
  have hh := congrArg List.toFinset he
  rw [← hl.1,← hr.1,list_map_toFinset] at hh
  exact hh

end WaveTurbulence.Reg.Skeleton
