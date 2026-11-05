/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeForestFactorization
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeMatchingFactorization

/-! # Exact single-slot raw factorization of the entire reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_raw {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    D.raw hS = ((D.eraseTree b).raw hS).insertChain
      (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b) := by
  apply Raw.ext
  · rfl
  · exact D.eraseTree_raw_forest hS b
  · exact D.eraseTree_raw_pairs hS b

end WaveTurbulence.Reg.Skeleton
