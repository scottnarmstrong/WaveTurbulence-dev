/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintJointFlip

/-! # Exact bilinear phase normalization for the frozen opposite gap sign -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2

/-- Simultaneously negating the source gap and joint coordinate preserves
the joint phase. -/
theorem joint_phase_neg_gap {d : ℕ} (r x : Mom d) :
    inner ℝ (-r) (-x) = inner ℝ r x := by
  rw [inner_neg_left,inner_neg_right,neg_neg]

/-- Negate free coefficients and retain the gap coefficient. This is the
exact sign transformation of every rung zeta and core xi form. -/
theorem linear_phase_neg_gap {d : ℕ} {ι : Type*} [Fintype ι]
    (r : Mom d) (z : ι → ℤ) (x : ι → Mom d) (q : ℤ) :
    inner ℝ (-r) ((∑ i, (z i : ℝ) • x i) + (q : ℝ) • (-r)) =
      inner ℝ r ((∑ i, ((-z i : ℤ) : ℝ) • x i) + (q : ℝ) • r) := by
  simp only [inner_neg_left,Int.cast_neg,neg_smul,smul_neg,Finset.sum_neg_distrib]
  simp only [inner_add_right,inner_neg_right]
  ring

end WaveTurbulence.VineEstS2
