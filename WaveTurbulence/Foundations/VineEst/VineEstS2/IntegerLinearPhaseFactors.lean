/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Recover primitive integer local factors from a pure phase identity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
variable {α : Type*} [Fintype α] [DecidableEq α]

def integerLinearForm (a x : α → ℤ) : ℤ := ∑ k, a k*x k

theorem integerLinearForm_single (a : α → ℤ) (i : α) :
    integerLinearForm a (Pi.single i 1) = a i := by
  classical
  simp [integerLinearForm,Pi.single_apply]

omit [DecidableEq α] in
theorem integerLinearForm_add (a x y : α → ℤ) :
    integerLinearForm a (x+y) = integerLinearForm a x+integerLinearForm a y := by
  simp only [integerLinearForm,Pi.add_apply,mul_add,Finset.sum_add_distrib]

end WaveTurbulence.VineEstS2
