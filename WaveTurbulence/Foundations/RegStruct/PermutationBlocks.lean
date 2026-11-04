/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.List.Perm.Basic

/-! # Moving a newly inserted pair block through unchanged context blocks -/

public section
namespace WaveTurbulence.Reg

/-- Lift a permutation in the first of three blocks, moving its extra suffix to the end. -/
theorem perm_lift_first {α : Type*} (A' A B C N : List α) (h : A'.Perm (A ++ N)) :
    (A' ++ B ++ C).Perm ((A ++ B ++ C) ++ N) := by
  apply ((h.append_right B).append_right C).trans
  simpa only [List.append_assoc] using
    ((List.perm_append_comm : (N ++ (B ++ C)).Perm ((B ++ C) ++ N)).append_left A)

/-- Lift a permutation in the middle of three blocks. -/
theorem perm_lift_middle {α : Type*} (A B' B C N : List α) (h : B'.Perm (B ++ N)) :
    (A ++ B' ++ C).Perm ((A ++ B ++ C) ++ N) := by
  apply ((h.append_left A).append_right C).trans
  simpa only [List.append_assoc] using
    ((List.perm_append_comm : (N ++ C).Perm (C ++ N)).append_left (A ++ B))

/-- Lift a permutation in the last of three blocks. -/
theorem perm_lift_last {α : Type*} (A B C' C N : List α) (h : C'.Perm (C ++ N)) :
    (A ++ B ++ C').Perm ((A ++ B ++ C) ++ N) := by
  simpa only [List.append_assoc] using h.append_left (A ++ B)

end WaveTurbulence.Reg
