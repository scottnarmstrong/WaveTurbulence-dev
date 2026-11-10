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

end WaveTurbulence.RegRed
