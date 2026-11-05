/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PinnedRelocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # Recursive transport of attachment positions from literal local hole equations -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Conditional geometric helper: local hole transport propagates through the original forest. -/
theorem inflatedPosition_transport_of_local_holes {w : ℕ} {S : Garden w}
    (D E : ReconstructionData S) (target : Address w) (m : MiniTreeCode)
    (h : ∀ b : GBranch S.tree,
      addrExt (pinnedRelocate target m (inflatedPosition S D.tree b.toNode))
        (E.tree b).lonePath = relocate target m.c m.lone (D.corePosition b))
    (a : GNode S.tree) :
    inflatedPosition S E.tree a = pinnedRelocate target m (inflatedPosition S D.tree a) := by
  by_cases hp : a.1.2 = []
  · have ha : a = GNode.root S.tree a.1.1 := Subtype.ext (Prod.ext rfl hp)
    rw [ha,inflatedPosition_root,inflatedPosition_root]
    by_cases he : (a.1.1,([] : Path)) = target
    · rw [pinnedRelocate,ite_eq_left he]
    · rw [pinnedRelocate,ite_eq_right he]
      symm
      apply BContext.relocate_eq_of_not_below
      intro hb
      have ht : target.2 = [] := List.eq_nil_of_prefix_nil hb.2
      exact he (Prod.ext hb.1 ht.symm)
  · let b := a.parent hp
    let i := a.1.2.getLast hp
    have ha : b.child i = a := child_parent a hp
    have ih := inflatedPosition_transport_of_local_holes D E target m h b.toNode
    have hc : E.corePosition b = relocate target m.c m.lone (D.corePosition b) := by
      unfold ReconstructionData.corePosition
      rw [ih]
      exact h b
    rw [← ha,E.core_child_position,D.core_child_position,hc,pinnedRelocate_child]
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

end WaveTurbulence.Reg.Skeleton
