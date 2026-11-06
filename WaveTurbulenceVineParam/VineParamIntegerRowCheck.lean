/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! # A fixed-carrier kernel checker for finite integer rows

The decision is constructed once on canonical Fin→Int functions. Concrete
matrix certificates supply a checked Boolean equality, so dependent matrix
index aliases never enter typeclass synthesis at a consumer site.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- The canonical constructive decision for equality of two finite integer rows. -/
@[expose] def integerRowDecision {n : ℕ} (f g : Fin n → ℤ) : Decidable (∀ j,f j=g j) := inferInstance

/-- A kernel computation certifying the canonical row decision proves the
entire row equality. No external checker or additional axiom is used. -/
theorem integer_row_eq_of_decide {n : ℕ} (f g : Fin n → ℤ)
    (h : @decide (∀ j,f j=g j) (integerRowDecision f g)=true) : ∀ j,f j=g j :=
  @of_decide_eq_true (∀ j,f j=g j) (integerRowDecision f g) h

end WaveTurbulence.Vine.Param
