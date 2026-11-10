/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Quadratic exponential sums

We use the convention `e(t) = exp(2πit)` and inclusive integer intervals, as
in DH23 equation `huagausssum`. The geometric-series estimate is the first
ingredient in Weyl differencing; no rational-approximation estimate is assumed.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- The additive exponential `exp(2πit)`. -/
@[expose] noncomputable def e (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem norm_e (t : ℝ) : ‖e t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  simp only [e, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem e_sub (s t : ℝ) : e (s - t) = e s / e t := by
  simp only [e, mul_sub, Complex.ofReal_sub, sub_mul, Complex.exp_sub]

theorem e_nat_mul (t : ℝ) (n : ℕ) : e ((n : ℝ) * t) = e t ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring


end WaveTurbulence.WeylSums
