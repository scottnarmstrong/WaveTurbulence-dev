/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarBracketTriangle
import Mathlib.Tactic

/-!
# Pointwise distribution of a convolution output weight

The output bracket is controlled by the larger input bracket. Distributing
the weight between the two possible larger inputs leaves two integrable
products at a common combined exponent.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Distribute a nonnegative output weight to the larger input bracket. -/
theorem scalar_kernel_weighted_product_le (p q r x y : ℝ) (hr : 0 ≤ r) :
    scalarBracket (x+y)^r * scalarBracket x^(-p) * scalarBracket y^(-q) ≤
      (3:ℝ)^r * (scalarBracket x^(-(p-r))*scalarBracket y^(-q) +
        scalarBracket x^(-p)*scalarBracket y^(-(q-r))) := by
  have hx : 0 < scalarBracket x := zero_lt_one.trans_le (one_le_scalarBracket _)
  have hy : 0 < scalarBracket y := zero_lt_one.trans_le (one_le_scalarBracket _)
  have hs : 0 ≤ scalarBracket (x+y) := zero_le_one.trans (one_le_scalarBracket _)
  have hxp : 0 ≤ scalarBracket x^(-p) := Real.rpow_nonneg hx.le _
  have hyp : 0 ≤ scalarBracket y^(-q) := Real.rpow_nonneg hy.le _
  have h3 : 0 ≤ (3:ℝ)^r := Real.rpow_nonneg (by norm_num) _
  have he (z a : ℝ) : scalarBracket z^r * scalarBracket z^(-a) =
      scalarBracket z^(-(a-r)) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le (one_le_scalarBracket _))]
    congr 1
    ring
  by_cases hxy : scalarBracket y ≤ scalarBracket x
  · have hb : scalarBracket (x+y) ≤ 3*scalarBracket x := by
      simpa only [max_eq_left hxy] using scalarBracket_add_le_three_max x y
    have hp := Real.rpow_le_rpow hs hb hr
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hx.le] at hp
    have ht := mul_le_mul_of_nonneg_right hp (mul_nonneg hxp hyp)
    calc
      _ ≤ ((3:ℝ)^r*scalarBracket x^r)*(scalarBracket x^(-p)*scalarBracket y^(-q)) := by
        convert ht using 1; ring
      _ = (3:ℝ)^r*(scalarBracket x^(-(p-r))*scalarBracket y^(-q)) := by
        calc
          _ = (3:ℝ)^r*((scalarBracket x^r*scalarBracket x^(-p))*scalarBracket y^(-q)) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hxp (Real.rpow_nonneg hy.le _))) h3
  · have hyx : scalarBracket x ≤ scalarBracket y := (lt_of_not_ge hxy).le
    have hb : scalarBracket (x+y) ≤ 3*scalarBracket y := by
      simpa only [max_eq_right hyx] using scalarBracket_add_le_three_max x y
    have hp := Real.rpow_le_rpow hs hb hr
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hy.le] at hp
    have ht := mul_le_mul_of_nonneg_right hp (mul_nonneg hxp hyp)
    calc
      _ ≤ ((3:ℝ)^r*scalarBracket y^r)*(scalarBracket x^(-p)*scalarBracket y^(-q)) := by
        convert ht using 1; ring
      _ = (3:ℝ)^r*(scalarBracket x^(-p)*scalarBracket y^(-(q-r))) := by
        calc
          _ = (3:ℝ)^r*(scalarBracket x^(-p)*(scalarBracket y^r*scalarBracket y^(-q))) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hx.le _) hyp)) h3

end WaveTurbulence.SumintPar
