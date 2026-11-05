/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Splice

/-! # Splicing creates no new inactive port outside the deleted pair -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- A surviving port is inactive after splicing exactly when it was inactive before. -/
theorem splice_fixed_iff {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b x : α) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    splice m a b x = x ↔ m x = x := by
  constructor
  · intro h
    by_cases hma : m x = a
    · have hx : m a = x := by have he := hm x; rw [hma] at he; exact he
      have hb : m b = x := by simpa [splice,hxa,hxb,hma] using h
      exact (hab (hm.injective (hx.trans hb.symm))).elim
    by_cases hmb : m x = b
    · have hx : m b = x := by have he := hm x; rw [hmb] at he; exact he
      have ha : m a = x := by simpa [splice,hxa,hxb,hmb,Ne.symm hab] using h
      exact (hab (hm.injective (ha.trans hx.symm))).elim
    · simpa [splice,hxa,hxb,hma,hmb] using h
  · exact splice_fixed m a b x

/-- In particular every surviving active halfedge remains active. -/
theorem splice_active {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b x : α) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hx : m x ≠ x) : splice m a b x ≠ x :=
  fun he => hx ((splice_fixed_iff m hm a b x hab hxa hxb).mp he)

end WaveTurbulence.Reg.Skeleton
