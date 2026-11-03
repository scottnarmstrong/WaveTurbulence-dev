/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# Factorial bounds for the simplex-volume argument

The elementary exponential-series bound used at TARGET L2035–2036.
The index restriction is explicit: for `z < d`, the same formula needs
`x ≥ 1`, since natural-number subtraction is truncated.
-/

public section

namespace WaveTurbulence.Analysis

/-- TARGET L2035–2036, in the range `d ≤ z`. -/
theorem pow_div_sub_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) {z d : ℕ} (hdz : d ≤ z) :
    x ^ z / (Nat.factorial (z - d) : ℝ) ≤ x ^ d * Real.exp x := by
  have he : d + (z - d) = z := Nat.add_sub_of_le hdz
  calc
    x ^ z / (Nat.factorial (z - d) : ℝ) =
        x ^ d * (x ^ (z - d) / (Nat.factorial (z - d) : ℝ)) := by
      have hpow : x ^ z = x ^ d * x ^ (z - d) := by rw [← pow_add, he]
      rw [hpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp x hx (z - d))
      (pow_nonneg hx d)

/-- The version valid for all indices when `x ≥ 1`. -/
theorem pow_div_sub_factorial_le_exp_of_one_le {x : ℝ} (hx : 1 ≤ x) (z d : ℕ) :
    x ^ z / (Nat.factorial (z - d) : ℝ) ≤ x ^ d * Real.exp x := by
  by_cases hdz : d ≤ z
  · exact pow_div_sub_factorial_le_exp (zero_le_one.trans hx) hdz
  · have hzd : z ≤ d := le_of_lt (Nat.lt_of_not_ge hdz)
    rw [Nat.sub_eq_zero_of_le hzd]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    exact (pow_le_pow_right₀ hx hzd).trans
      (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hx) d)
        (Real.one_le_exp (zero_le_one.trans hx)))

end WaveTurbulence.Analysis
