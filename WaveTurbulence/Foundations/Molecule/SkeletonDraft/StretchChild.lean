/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Ordered-child transport away from the collapsed interval boundary -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem below_child_iff {w : ℕ} (a d : Address w) (i : Fin 3) (hne : addrExt d [i] ≠ a) :
    Below a (addrExt d [i]) ↔ Below a d := by
  constructor
  · intro h
    have hlen := h.2.length_le
    change a.2.length ≤ (d.2 ++ [i]).length at hlen
    by_cases hl : a.2.length ≤ d.2.length
    · exact ⟨h.1,List.prefix_of_prefix_length_le h.2 (List.prefix_append _ _) hl⟩
    · have he : a.2.length = (d.2 ++ [i]).length := by simp only [List.length_append,List.length_singleton] at *; omega
      exact (hne (Prod.ext h.1 (h.2.eq_of_length he).symm)).elim
  · intro h
    exact ⟨h.1,h.2.trans (List.prefix_append _ _)⟩

/-- Prefix insertion commutes with a child step except when that step lands exactly at the upper root. -/
theorem stretch_child {w : ℕ} (a d : Address w) (p : Path) (i : Fin 3)
    (hne : addrExt d [i] ≠ a) :
    stretch a p (addrExt d [i]) = addrExt (stretch a p d) [i] := by
  by_cases hd : Below a d
  · obtain ⟨r,rfl⟩ := below_exists_frame a d hd
    rw [addrExt_append,stretch_frame,stretch_frame,addrExt_append]
    simp only [List.append_assoc]
  · have hc : ¬ Below a (addrExt d [i]) := fun he => hd ((below_child_iff a d i hne).mp he)
    rw [stretch_outside a p _ hc,stretch_outside a p _ hd]

end WaveTurbulence.Reg.Skeleton
