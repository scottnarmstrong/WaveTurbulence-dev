/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Extended nonnegative algebra for the weighted angular Schur test
-/

public section

open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Squaring the nonnegative extended square root recovers its argument. -/
theorem ennreal_half_sq (x : ℝ≥0∞) : (x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- Moving the two finite radial weights onto the opposite angular factors. -/
theorem ennreal_schur_pairing (E F A B : ℝ≥0∞) :
    (E ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2)) *
      (F ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) =
      (E * B) ^ ((1 : ℝ) / 2) * (F * A) ^ ((1 : ℝ) / 2) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  ac_rfl

/-- The square root of a finite real square is its nonnegative value. -/
theorem ennreal_ofReal_sq_half (x : ℝ) (hx : 0 ≤ x) :
    (ENNReal.ofReal (x ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_pow hx 2, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- The two square roots of the Schur constant combine to one constant. -/
theorem ennreal_schur_norm_constant (C : ℝ≥0∞) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (C * ENNReal.ofReal (x ^ 2)) ^ ((1 : ℝ) / 2) *
      (C * ENNReal.ofReal (y ^ 2)) ^ ((1 : ℝ) / 2) = C * ENNReal.ofReal (x * y) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ennreal_ofReal_sq_half x hx, ennreal_ofReal_sq_half y hy]
  calc
    _ = (C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) *
        (ENNReal.ofReal x * ENNReal.ofReal y) := by ac_rfl
    _ = _ := by rw [← pow_two, ← ENNReal.rpow_two, ennreal_half_sq, ENNReal.ofReal_mul hx]

end WaveTurbulence.WKEL2
