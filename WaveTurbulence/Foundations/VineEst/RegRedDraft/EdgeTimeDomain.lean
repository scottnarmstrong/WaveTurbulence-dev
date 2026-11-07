/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeParentClocks
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.TimeDomain

/-! # Source time domains with one exterior upper clock per actual tree -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem parentClockWith_nonroot {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (a : GNode tree) (ha : a.1.2 ≠ []) :
    parentClockWith top τ a = τ (a.parent ha) := by
  rw [parentClockWith,nodeToSlot,dite_eq_right ha]

theorem lt_rootTop_of_lt_parentClockWith {w : ℕ} {tree : Fin w → TTree} (top : Fin w → ℝ)
    (τ : GBranch tree → ℝ) (h : ∀ b, τ b < parentClockWith top τ b.toNode)
    (b : GBranch tree) : τ b < top b.1.1 := by
  by_cases hb : b.1.2 = []
  · have he : b.toNode = GNode.root tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
    have ht := h b
    rw [he,parentClockWith_root] at ht
    exact ht
  · have ht := h b
    change τ b < parentClockWith top τ b.toNode at ht
    rw [parentClockWith_nonroot top τ b.toNode hb] at ht
    exact ht.trans (lt_rootTop_of_lt_parentClockWith top τ h (b.toNode.parent hb))
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hp : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

def edgeTimeDomain {w : ℕ} (LG : LayeredGarden w) (top : Fin w → ℝ) (s : ℝ) :
    Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b ∧
    τ b < parentClockWith top τ b.toNode ∧ (LG.garden.IsLoneParent b → s < τ b)}

/-- The native KQstar/KTstar domains have their literal source meaning in
immediate-parent coordinates, with a separate exterior clock for each root. -/
theorem kDomain_eq_edgeTimeDomain {w : ℕ} (LG : LayeredGarden w) (top : Fin w → ℝ) (s : ℝ) :
    kDomain LG (fun b => top b.1.1) s = edgeTimeDomain LG top s := by
  ext τ
  constructor
  · intro h b
    refine ⟨(h b).1,(h b).2.1,(h b).2.2.1,?_,(h b).2.2.2.2.2⟩
    by_cases hb : b.1.2 = []
    · have he : b.toNode = GNode.root LG.garden.tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
      rw [he,parentClockWith_root]
      exact (h b).2.2.2.1
    · have hc : b.IsChildOf (b.toNode.parent hb) :=
        ⟨rfl,b.1.2.getLast hb,(List.dropLast_append_getLast hb).symm⟩
      change τ b < parentClockWith top τ b.toNode
      rw [parentClockWith_nonroot top τ b.toNode hb]
      exact (h (b.toNode.parent hb)).2.2.2.2.1 b hc
  · intro h b
    refine ⟨(h b).1,(h b).2.1,(h b).2.2.1,
      lt_rootTop_of_lt_parentClockWith top τ (fun b => (h b).2.2.2.1) b,?_,(h b).2.2.2.2⟩
    intro c hc
    obtain ⟨i,hi⟩ := branch_eq_child_of_isChildOf hc
    have ht := (h c).2.2.2.1
    rw [hi,parentClockWith_child] at ht
    exact ht

end WaveTurbulence.RegRed
