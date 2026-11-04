/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Fixed derivative and summation losses remain geometric in the order

DH23 Prop6.1: root derivatives up to40d distribute over2n+1 input
factors. A fixed polynomial in the order is absorbed into the permitted
C^n constant, independently of the logarithmic order exponent.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- Fixed powers of the leaf count cost only a geometric order factor. -/
theorem leaf_polynomial_le_geometric (n K : ℕ) :
    (2 * (n : ℝ) + 1) ^ K ≤ ((3 : ℝ) ^ K) ^ n := by
  have h : 2 * (n : ℝ) + 1 ≤ 3 ^ n := by
    have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 2) n
    simpa only [show (1 : ℝ)+2 = 3 by norm_num,mul_comm,add_comm] using h
  exact (pow_le_pow_left₀ (by positivity) h K).trans_eq (pow_right_comm _ _ _)

end WaveTurbulence.RegAsymp
