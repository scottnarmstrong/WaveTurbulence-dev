/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestBranches

/-! # Actual mini pieces inside an induced source subforest remain actual ambient mini pieces -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subforest_branch_node {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (b : GBranch E.shape) : E.nodeEmbedding b.toNode = (subforestBranchEmbedding E b).toNode :=
  Subtype.ext rfl

theorem subforest_leaf_node {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (ℓ : GLeaf E.shape) : (E.leafEmbedding ℓ).toNode = E.nodeEmbedding ℓ.toNode := Subtype.ext rfl

end WaveTurbulence.Reg.Skeleton
