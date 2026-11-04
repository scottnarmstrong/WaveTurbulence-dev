/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleDualDerivativeNumerics
import Mathlib.Tactic

/-!
# Common phase scale for the actual circle dual derivative formulas

The scalar derivative comparisons normalize to a common scale and fixed
absolute comparison constants. This prepares the derivative A-estimate;
no circle phase or B-process result is introduced here.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Normalize any of the three derivative magnitude comparisons to phase
scale `A/(32768Y)` and length scale `2Y`. -/
theorem circle_dual_normalized_derivative_comparison {A Y v : ℝ}
    (hA : 0 < A) (hY : 0 < Y) (k : ℕ) (hk : k ≤ 5)
    (hb : A/(32768*Y^(k+1)) ≤ v ∧ v ≤ 3840*A/Y^(k+1)) :
    v ∈ Set.Icc ((A/(32768*Y))/(2*Y)^k)
      (4294967296*((A/(32768*Y))/(2*Y)^k)) := by
  let t : ℝ := A/Y^(k+1)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hp : 0 < (2:ℝ)^k := by positivity
  have hp1 : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hp32 : (2:ℝ)^k ≤ 32 := by
    simpa only [show (2:ℝ)^5 = 32 by norm_num] using
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk
  have he : (A/(32768*Y))/(2*Y)^k = t/(32768*(2:ℝ)^k) := by
    dsimp only [t]
    rw [mul_pow,pow_succ]
    field_simp
  rw [he]
  constructor
  · calc
      _ ≤ t/32768 := div_le_div_of_nonneg_left ht.le (by norm_num)
        (by nlinarith only [hp1])
      _ = A/(32768*Y^(k+1)) := by dsimp only [t]; ring
      _ ≤ v := hb.1
  · have hv : v ≤ 3840*t := by simpa only [t,mul_div_assoc] using hb.2
    apply hv.trans
    conv_rhs => rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 32768*(2:ℝ)^k)).mpr
    have hc : 3840*(32768*(2:ℝ)^k) ≤ 4294967296 := by nlinarith only [hp32]
    nlinarith only [mul_le_mul_of_nonneg_right hc ht.le]

/-- The dual frequency range supplies the common phase-scale condition
with a fixed absolute comparison factor. -/
theorem circle_dual_normalized_frequency_comparison {A Y : ℝ}
    (hY : 0 < Y) (hAY : Y^2 ≤ A) : 2*Y ≤ 65536*(A/(32768*Y)) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 32768*Y)).mpr
  nlinarith only [hAY]

end WaveTurbulence.NumberTheory
