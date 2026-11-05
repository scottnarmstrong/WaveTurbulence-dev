/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions

/-! # Attachment positions depend only on strict actual source ancestors -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_congr_ancestors {w : ℕ} (S : Garden w)
    (X Y : GBranch S.tree → RegChain) (a : GNode S.tree)
    (ht : ∀ b : GBranch S.tree, Below b.1 a.1 → b.1.2.length < a.1.2.length → X b = Y b) :
    inflatedPosition S X a = inflatedPosition S Y a := by
  by_cases hp : a.1.2 = []
  · rw [inflatedPosition,dite_eq_left hp,inflatedPosition,dite_eq_left hp]
  · let b := a.parent hp
    have hb : Below b.1 a.1 := by
      have he := congrArg (fun z : GNode S.tree => z.1) (child_parent a hp)
      exact he ▸ below_extend b.1 [a.1.2.getLast hp]
    have hlen : b.1.2.length < a.1.2.length := by
      change a.1.2.dropLast.length < a.1.2.length
      rw [List.length_dropLast]
      have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
      omega
    have hparent : inflatedPosition S X b.toNode = inflatedPosition S Y b.toNode :=
      inflatedPosition_congr_ancestors S X Y b.toNode (fun c hc hcl => by
        change c.1.2.length < b.1.2.length at hcl
        exact ht c (below_trans hc hb) (Nat.lt_trans hcl hlen))
    conv_lhs => rw [inflatedPosition,dite_eq_right hp]
    conv_rhs => rw [inflatedPosition,dite_eq_right hp]
    exact congrArg₂ addrExt hparent
      (congrArg (fun Z : RegChain => Z.lonePath ++ [a.1.2.getLast hp]) (ht b hb hlen))
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  rw [List.length_dropLast]
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  omega

end WaveTurbulence.Reg.Skeleton
