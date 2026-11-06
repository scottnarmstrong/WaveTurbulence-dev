/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBarePairForest
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBarePairMatching

/-! # Complete literal outer/inner/rest factorization of a bare pair constructor -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.insertChain_pair {w : ℕ} (R : Raw w) (a : Address w)
    (ha : a.2 ∈ (R.tree a.1).nodes) (m : MiniTreeCode) (X Y : RegChain) :
    (((R.opB a m).insertChain (addrExt a [m.c]) X).insertChain
      (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])) Y) =
        R.insertChain a (.pair m .triv .triv X Y) := by
  apply Raw.ext
  · rfl
  · exact R.insertChain_pair_forest a ha m X Y
  · exact R.insertChain_pair_matching a m X Y

end WaveTurbulence.Reg.Skeleton
