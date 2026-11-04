/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairKernels
import Mathlib.Tactic

/-!
# Fractional moments needed for bad and incoherent factors

Every nonnegative moment of order at most one is controlled by the
ordinary first moment. The exact scaling factor is retained for case (c).
-/

public section

namespace WaveTurbulence.Sumint

/-- Sublinear nonnegative powers are bounded by one plus the base. -/
theorem rpow_le_one_add {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    x^p ≤ 1+x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hp).trans (by linarith)
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hp1
    rw [Real.rpow_one] at hh
    linarith

/-- Rescaling a fractional gap moment retains the precise negative power
of the time scale, while costing at most one first moment. -/
theorem abs_div_rpow_le_first_moment {c p : ℝ} (hc : 0 < c)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    |s/c|^p ≤ c^(-p)*(1+|s|) := by
  rw [abs_div, abs_of_pos hc, Real.div_rpow (abs_nonneg s) hc.le,
    div_eq_inv_mul, ← Real.rpow_neg hc.le]
  exact mul_le_mul_of_nonneg_left (rpow_le_one_add (abs_nonneg s) hp hp1)
    (Real.rpow_nonneg hc.le _)

end WaveTurbulence.Sumint
