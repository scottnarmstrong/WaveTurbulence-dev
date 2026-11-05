/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchChild

/-! # Actual source ancestry is preserved by regular-tree attachment positions -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_below {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a b : GNode S.tree) (hab : Below a.1 b.1) :
    Below (inflatedPosition S X a) (inflatedPosition S X b) := by
  by_cases he : a = b
  · subst b
    exact ⟨rfl,List.prefix_refl _⟩
  · have hb : b.1.2 ≠ [] := by
      intro hb
      have ha : a.1.2 = [] := List.prefix_nil.mp (by simpa only [hb] using hab.2)
      exact he (Subtype.ext (Prod.ext hab.1.symm (ha.trans hb.symm)))
    let d := b.parent hb
    let i := b.1.2.getLast hb
    have hc : d.child i = b := child_parent b hb
    have hcv : addrExt d.1 [i] = b.1 := congrArg (fun z : GNode S.tree => z.1) hc
    have hn : addrExt d.1 [i] ≠ a.1 := fun hh => he (Subtype.ext (hh.symm.trans hcv))
    have hd : Below a.1 d.1 := (below_child_iff a.1 d.1 i hn).mp (by rw [hcv]; exact hab)
    have hi := inflatedPosition_below S X a d.toNode hd
    have ht : Below (inflatedPosition S X d.toNode) (inflatedPosition S X b) := by
      rw [← hc,inflatedPosition_child]
      exact below_extend _ _
    exact below_trans hi ht
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hn : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

end WaveTurbulence.Reg.Skeleton
