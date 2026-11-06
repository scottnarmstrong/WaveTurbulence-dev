/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions

/-! # Reconstructed attachment positions depend only on the branch-code lone paths -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_congr_lonePath {w : ℕ} (S : Garden w)
    (X Y : GBranch S.tree → RegChain) (h : ∀ b, (X b).lonePath = (Y b).lonePath)
    (a : GNode S.tree) : inflatedPosition S X a = inflatedPosition S Y a := by
  by_cases hp : a.1.2 = []
  · conv_lhs => rw [inflatedPosition,dite_eq_left hp]
    conv_rhs => rw [inflatedPosition,dite_eq_left hp]
  · conv_lhs => rw [inflatedPosition,dite_eq_right hp]
    conv_rhs => rw [inflatedPosition,dite_eq_right hp]
    exact congrArg₂ addrExt (inflatedPosition_congr_lonePath S X Y h (a.parent hp).toNode)
      (congrArg (fun p => p ++ [a.1.2.getLast hp]) (h (a.parent hp)))
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  rw [List.length_dropLast]
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  omega

end WaveTurbulence.Reg.Skeleton
