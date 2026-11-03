/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Polynomial square-root denominator bounds on dyadic intervals

These scalar inequalities normalize the third/fourth/fifth derivative
formulas of the circular dual curve. They define no phase and no analytic
class, and do not assert a Poisson or stationary-phase transformation.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Uniform denominator comparison on `[Y,4Y]`, including two extra sample
units for any block of scale at least one. -/
theorem sqrt_quadratic_denominator_bounds {h Y x : ℝ} (hh : 0 < h) (hY : h ≤ Y)
    (hx : x ∈ Set.Icc Y (4*Y)) (m : ℕ) :
    Y^(2*m+1) ≤ (h^2+x^2)^m*Real.sqrt (h^2+x^2) ∧
      (h^2+x^2)^m*Real.sqrt (h^2+x^2) ≤ (5*(17:ℝ)^m)*Y^(2*m+1) := by
  have hYp : 0 < Y := hh.trans_le hY
  have hxp : 0 < x := hYp.trans_le hx.1
  have hD : 0 < h^2+x^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  have hlo : Y^2 ≤ h^2+x^2 := by nlinarith only [hYp.le,hx.1,sq_nonneg h]
  have hhi : h^2+x^2 ≤ 17*Y^2 := by nlinarith only [hh.le,hY,hxp.le,hx.2,hYp.le]
  have hslo : Y ≤ Real.sqrt (h^2+x^2) := Real.le_sqrt_of_sq_le hlo
  have hshi : Real.sqrt (h^2+x^2) ≤ 5*Y := Real.sqrt_le_iff.mpr
    ⟨by positivity,by nlinarith only [hhi,sq_nonneg Y]⟩
  have hpLo := pow_le_pow_left₀ (sq_nonneg Y) hlo m
  have hpHi := pow_le_pow_left₀ hD.le hhi m
  have hid : (Y^2)^m*Y = Y^(2*m+1) := by rw [pow_add,pow_mul,pow_one]
  constructor
  · rw [← hid]
    exact mul_le_mul hpLo hslo hYp.le (pow_nonneg hD.le m)
  · have he : (17*Y^2)^m*(5*Y) = (5*(17:ℝ)^m)*Y^(2*m+1) := by
      rw [mul_pow,← hid]
      ring
    rw [← he]
    exact mul_le_mul hpHi hshi (Real.sqrt_nonneg _) (pow_nonneg (by positivity : 0 ≤ 17*Y^2) m)

/-- A scalar quotient comparison used to keep the derivative normalization
constants uniform across derivative orders three, four and five. -/
theorem quotient_bounds_of_power_comparisons {Y A num den l u v : ℝ} (k m : ℕ)
    (hY : 0 < Y) (hA : 0 < A)
    (hnumLo : l*A*Y^m ≤ num) (hnumHi : num ≤ u*A*Y^m)
    (hdenLo : Y^(k+m) ≤ den) (hdenHi : den ≤ v*Y^(k+m))
    (hvl : v ≤ 32768*l) (hu : u ≤ 3840) :
    A/(32768*Y^k) ≤ num/den ∧ num/den ≤ 3840*A/Y^k := by
  have hd : 0 < den := (pow_pos hY _).trans_le hdenLo
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 32768*Y^k) hd).mpr
    calc
      _ ≤ A*(v*Y^(k+m)) := mul_le_mul_of_nonneg_left hdenHi hA.le
      _ ≤ A*((32768*l)*Y^(k+m)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hvl (pow_nonneg hY.le _)) hA.le
      _ = (l*A*Y^m)*(32768*Y^k) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnumLo (by positivity)
  · apply (div_le_div_iff₀ hd (pow_pos hY k)).mpr
    calc
      _ ≤ (u*A*Y^m)*Y^k := mul_le_mul_of_nonneg_right hnumHi (pow_nonneg hY.le _)
      _ = u*(A*Y^(k+m)) := by rw [pow_add]; ring
      _ ≤ 3840*(A*Y^(k+m)) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = (3840*A)*Y^(k+m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdenLo (by positivity)

end WaveTurbulence.NumberTheory
