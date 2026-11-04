/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairKernels
import Mathlib.Tactic

/-!
# A scalar bracket bound in terms of the larger summand

A fixed factor three is sufficient for the convolution estimates. The
constant is absolute and independent of every source parameter.
-/

public section

namespace WaveTurbulence.Sumint

/-- The scalar Japanese bracket is bounded by one plus the absolute value. -/
theorem scalarBracket_le_one_add_abs (s : ℝ) : scalarBracket s ≤ 1+|s| := by
  unfold scalarBracket
  apply (Real.sqrt_le_left (by positivity : 0 ≤ 1+|s|)).mpr
  nlinarith [sq_abs s, abs_nonneg s]

/-- A sum's bracket is bounded by three times the larger summand bracket. -/
theorem scalarBracket_add_le_three_max (x y : ℝ) :
    scalarBracket (x+y) ≤ 3*max (scalarBracket x) (scalarBracket y) := by
  have hx := abs_le_scalarBracket x
  have hy := abs_le_scalarBracket y
  have h1 := one_le_scalarBracket x
  have hm1 := le_max_left (scalarBracket x) (scalarBracket y)
  have hm2 := le_max_right (scalarBracket x) (scalarBracket y)
  have hh := (scalarBracket_le_one_add_abs (x+y)).trans
    (add_le_add (le_refl (1:ℝ)) (abs_add_le x y))
  linarith

end WaveTurbulence.Sumint
