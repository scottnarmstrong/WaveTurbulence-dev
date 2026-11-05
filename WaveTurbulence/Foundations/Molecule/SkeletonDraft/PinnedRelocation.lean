/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchChild
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry

/-! # Attachment transport pins the insertion's own upper boundary -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Upper attachments stay at the insertion boundary; all other addresses relocate. -/
def pinnedRelocate {w : ℕ} (target : Address w) (m : MiniTreeCode) (a : Address w) : Address w :=
  if a = target then a else relocate target m.c m.lone a

/-- A boundary at or above the inserted node keeps its own upper attachment. -/
theorem pinnedRelocate_of_below {w : ℕ} (target a : Address w) (m : MiniTreeCode)
    (h : Below a target) : pinnedRelocate target m a = a := by
  by_cases he : a = target
  · rw [pinnedRelocate,ite_eq_left he]
  · rw [pinnedRelocate,ite_eq_right he]
    apply BContext.relocate_eq_of_not_below
    intro hb
    have hl : a.2.length = target.2.length := Nat.le_antisymm h.2.length_le hb.2.length_le
    exact he (Prod.ext h.1.symm (h.2.eq_of_length hl))

theorem pinnedRelocate_of_not_below {w : ℕ} (target a : Address w) (m : MiniTreeCode)
    (h : ¬ Below target a) : pinnedRelocate target m a = a := by
  unfold pinnedRelocate
  split_ifs
  · rfl
  · exact BContext.relocate_eq_of_not_below _ _ _ _ h

theorem pinnedRelocate_eq_relocate {w : ℕ} (target a : Address w) (m : MiniTreeCode)
    (h : ¬ Below a target) : pinnedRelocate target m a = relocate target m.c m.lone a := by
  have he : a ≠ target := by
    intro he
    apply h
    rw [he]
    exact ⟨rfl,List.prefix_refl _⟩
  exact ite_eq_right he

/-- A single original child step starts below the relocated original core. -/
theorem pinnedRelocate_child {w : ℕ} (target a : Address w) (m : MiniTreeCode) (i : Fin 3) :
    pinnedRelocate target m (addrExt a [i]) = addrExt (relocate target m.c m.lone a) [i] := by
  by_cases he : addrExt a [i] = target
  · rw [pinnedRelocate,ite_eq_left he]
    have hn : ¬ Below target a := by
      intro h
      have hl := h.2.length_le
      rw [← he] at hl
      change (a.2 ++ [i]).length ≤ a.2.length at hl
      simp only [List.length_append,List.length_singleton] at hl
      omega
    rw [BContext.relocate_eq_of_not_below _ _ _ _ hn]
  · rw [pinnedRelocate,ite_eq_right he]
    exact stretch_child target a [m.c,m.lone] i he

end WaveTurbulence.Reg.Skeleton
