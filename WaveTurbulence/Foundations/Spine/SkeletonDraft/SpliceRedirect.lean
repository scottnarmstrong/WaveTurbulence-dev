/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceCommutation

/-! # Exact matching transport when a free attachment slot is replaced by its external partner -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

def redirect {α : Type*} [DecidableEq α] (b x r : α) : α := if r = b then x else r

/-- A free splice transports every surviving edge by replacing the second attachment slot
with the external partner of the first attachment slot. -/
theorem splice_redirect {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b x r : α) (hxa : x ≠ a) (hxb : x ≠ b)
    (hmx : m x = a) (hmb : m b ≠ b) (hra : r ≠ a) (hrx : r ≠ x) :
    splice m a b (redirect b x r) = redirect b x (m r) := by
  have hma : m a = x := by rw [← hmx,hm x]
  by_cases hrb : r = b
  · subst r
    simp only [redirect]
    simp [splice,hxa,hxb,hmx,hmb]
  · have hmra : m r ≠ a := fun he => hrx (hm.injective (he.trans hmx.symm))
    simp only [redirect,ite_eq_right hrb]
    by_cases hmrb : m r = b
    · rw [splice_outside m a b r hra hrb,ite_eq_right hmra,ite_eq_left hmrb,hma]
      simp [hmrb]
    · simp [splice,hra,hrb,hmra,hmrb]

end WaveTurbulence.Reg.Skeleton
