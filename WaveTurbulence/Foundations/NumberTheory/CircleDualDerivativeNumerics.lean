/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.SqrtQuadraticBounds
import Mathlib.Tactic

/-!
# Scalar normalization of the circle dual derivative formulas

The three explicit positive quotients are the magnitudes of derivatives
three, four and five of the circle dual. Their calculus identities belong
to VdCB; here only the scalar comparison inequalities are proved. No phase,
phase class, exponent pair or B-process transformation is defined.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Common comparison constants for the third-derivative quotient. -/
theorem circle_dual_third_quotient_bounds {R h Y x : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (4*Y)) :
    R*h^2/(32768*Y^4) ≤ (3*R*h^2*x)/((h^2+x^2)^2*Real.sqrt (h^2+x^2)) ∧
      (3*R*h^2*x)/((h^2+x^2)^2*Real.sqrt (h^2+x^2)) ≤ 3840*R*h^2/Y^4 := by
  have hYp : 0 < Y := hh.trans_le hY
  have hd := sqrt_quadratic_denominator_bounds hh hY hx 2
  norm_num at hd
  have hnlo : 3*(R*h^2)*Y^1 ≤ 3*R*h^2*x := by
    have he := mul_le_mul_of_nonneg_left hx.1 (by positivity : 0 ≤ 3*R*h^2)
    nlinarith only [he]
  have hnhi : 3*R*h^2*x ≤ 12*(R*h^2)*Y^1 := by
    have he := mul_le_mul_of_nonneg_left hx.2 (by positivity : 0 ≤ 3*R*h^2)
    nlinarith only [he]
  have he := quotient_bounds_of_power_comparisons (A := R*h^2) (l := 3) (u := 12) (v := 1445)
    4 1 hYp (by positivity) hnlo hnhi hd.1 hd.2 (by norm_num) (by norm_num)
  simpa only [mul_assoc] using! he

/-- Common comparison constants for the fourth-derivative quotient. -/
theorem circle_dual_fourth_quotient_bounds {R h Y x : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (4*Y)) :
    R*h^2/(32768*Y^5) ≤ (3*R*h^2*(4*x^2-h^2))/((h^2+x^2)^3*Real.sqrt (h^2+x^2)) ∧
      (3*R*h^2*(4*x^2-h^2))/((h^2+x^2)^3*Real.sqrt (h^2+x^2)) ≤ 3840*R*h^2/Y^5 := by
  have hYp : 0 < Y := hh.trans_le hY
  have hxp : 0 < x := hYp.trans_le hx.1
  have hxlo := pow_le_pow_left₀ hYp.le hx.1 2
  have hxhi := pow_le_pow_left₀ hxp.le hx.2 2
  have hhq := pow_le_pow_left₀ hh.le hY 2
  norm_num only [mul_pow,Nat.reducePow] at hxhi
  have hlo : 3*Y^2 ≤ 4*x^2-h^2 := by nlinarith only [hxlo,hhq]
  have hhi : 4*x^2-h^2 ≤ 64*Y^2 := by nlinarith only [hxhi,sq_nonneg h]
  have hd := sqrt_quadratic_denominator_bounds hh hY hx 3
  norm_num at hd
  have hnlo : 9*(R*h^2)*Y^2 ≤ 3*R*h^2*(4*x^2-h^2) := by
    have he := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 3*R*h^2)
    nlinarith only [he]
  have hnhi : 3*R*h^2*(4*x^2-h^2) ≤ 192*(R*h^2)*Y^2 := by
    have he := mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 3*R*h^2)
    nlinarith only [he]
  have he := quotient_bounds_of_power_comparisons (A := R*h^2) (l := 9) (u := 192) (v := 24565)
    5 2 hYp (by positivity) hnlo hnhi hd.1 hd.2 (by norm_num) (by norm_num)
  simpa only [mul_assoc] using! he

/-- Common comparison constants for the fifth-derivative magnitude. -/
theorem circle_dual_fifth_quotient_bounds {R h Y x : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (4*Y)) :
    R*h^2/(32768*Y^6) ≤ (15*R*h^2*x*(4*x^2-3*h^2))/((h^2+x^2)^4*Real.sqrt (h^2+x^2)) ∧
      (15*R*h^2*x*(4*x^2-3*h^2))/((h^2+x^2)^4*Real.sqrt (h^2+x^2)) ≤ 3840*R*h^2/Y^6 := by
  have hYp : 0 < Y := hh.trans_le hY
  have hxp : 0 < x := hYp.trans_le hx.1
  have hxlo := pow_le_pow_left₀ hYp.le hx.1 2
  have hxhi := pow_le_pow_left₀ hxp.le hx.2 2
  have hhq := pow_le_pow_left₀ hh.le hY 2
  norm_num only [mul_pow,Nat.reducePow] at hxhi
  have hlo : Y^2 ≤ 4*x^2-3*h^2 := by nlinarith only [hxlo,hhq]
  have hhi : 4*x^2-3*h^2 ≤ 64*Y^2 := by nlinarith only [hxhi,sq_nonneg h]
  have hd := sqrt_quadratic_denominator_bounds hh hY hx 4
  norm_num at hd
  have hnlo : 15*(R*h^2)*Y^3 ≤ 15*R*h^2*x*(4*x^2-3*h^2) := by
    have he := mul_le_mul hx.1 hlo (sq_nonneg Y) hxp.le
    have ht := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 15*R*h^2)
    nlinarith only [ht]
  have hnhi : 15*R*h^2*x*(4*x^2-3*h^2) ≤ 3840*(R*h^2)*Y^3 := by
    have he := mul_le_mul hx.2 hhi ((sq_nonneg Y).trans hlo) (by positivity : 0 ≤ 4*Y)
    have ht := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 15*R*h^2)
    nlinarith only [ht]
  have he := quotient_bounds_of_power_comparisons (A := R*h^2) (l := 15) (u := 3840) (v := 417605)
    6 3 hYp (by positivity) hnlo hnhi hd.1 hd.2 (by norm_num) (by norm_num)
  simpa only [mul_assoc] using! he

end WaveTurbulence.NumberTheory
