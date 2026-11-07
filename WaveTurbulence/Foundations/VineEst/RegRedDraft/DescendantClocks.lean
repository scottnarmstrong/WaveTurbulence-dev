/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.GluedAttachmentLabels
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks

/-! # Strict time ordering along actual tree paths and source attachment clocks -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem prefix_dropLast_of_ne {α : Type*} {p q : List α} (h : p <+: q) (hne : p ≠ q) :
    p <+: q.dropLast := by
  obtain ⟨r,rfl⟩ := h
  have hr : r ≠ [] := by intro he; apply hne; rw [he,List.append_nil]
  rw [List.dropLast_append_of_ne_nil hr]
  exact List.prefix_append _ _

/-- Every descendant branch precedes the incoming clock at the actual root of
its rooted subtree. The order is derived from immediate parent inequalities. -/
theorem branchTime_lt_parentClock_of_desc {w : ℕ} {tree : Fin w → TTree}
    (top : ℝ) (τ : GBranch tree → ℝ) (hτ : ∀ b, τ b < parentClock top τ b.toNode)
    (a : GNode tree) (b : GBranch tree) (hd : a.IsDesc b.toNode) :
    τ b < parentClock top τ a := by
  by_cases he : a.1.2 = b.1.2
  · have hab : a = b.toNode := Subtype.ext (Prod.ext hd.1 he)
    exact hab ▸ hτ b
  · have hb : b.1.2 ≠ [] := by
      intro hz
      have hp : a.1.2 <+: [] := hz ▸ hd.2
      apply he
      exact (List.prefix_nil.mp hp).trans hz.symm
    have hparent : a.IsDesc (b.toNode.parent hb).toNode :=
      ⟨hd.1,prefix_dropLast_of_ne hd.2 he⟩
    have ht := hτ b
    change τ b < parentClock top τ b.toNode at ht
    rw [parentClock_nonroot top τ b.toNode hb] at ht
    exact ht.trans (branchTime_lt_parentClock_of_desc top τ hτ a (b.toNode.parent hb) hparent)
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hp : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

/-- Incoming clocks at all actual attachment roots are precisely their original
skeleton parent clocks, including the exterior clock at original roots. -/
theorem parentClock_attachedNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) (a : GNode S.tree) :
    parentClock top τ (attachedNode D hS a) =
      parentClock top (fun b => τ (D.coreBranch hS b)) a := by
  obtain ⟨s,rfl⟩ := (nodeSlotEquiv S.tree).symm.surjective a
  rcases s with j | ⟨b,i⟩
  · exact (congrArg (parentClock top τ) (attachedNode_root D hS j)).trans
      (parentClock_root _ _ _ j)
  · exact (congrArg (parentClock top τ) (attachedNode_child D hS b i)).trans
      ((parentClock_child top τ _ i).trans (parentClock_child top (fun b => τ (D.coreBranch hS b)) b i).symm)

end WaveTurbulence.RegRed
