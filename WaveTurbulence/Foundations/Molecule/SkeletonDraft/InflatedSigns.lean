/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions

/-! # Every actual skeleton attachment retains its original root sign -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_sign {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a : GNode S.tree) : nodeSign S.sig (inflatedPosition S X a) = nodeSign S.sig a.1 := by
  rw [inflatedPosition]
  split_ifs with h
  · rfl
  · rw [nodeSign_addrExt,Comb.pathSign_append,lonePath_sign,
      inflatedPosition_sign S X (a.parent h).toNode,pathSign_singleton]
    have he := congrArg (fun z : GNode S.tree => nodeSign S.sig z.1) (child_parent a h)
    change nodeSign S.sig (addrExt (a.parent h).1 [a.1.2.getLast h]) = nodeSign S.sig a.1 at he
    rw [nodeSign_step] at he
    exact he
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hp : a.1.2.length ≠ 0 := fun he => h (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

end WaveTurbulence.Reg.Skeleton
