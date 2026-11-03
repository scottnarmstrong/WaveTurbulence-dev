/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularCauchyAlgebra

/-!
# Nonnegative factors for the gain Cauchy–Schwarz estimate
-/

public section

open scoped ENNReal

namespace WaveTurbulence.WKEL2

theorem ennreal_gain_factor_sq (x a : ℝ≥0∞) :
    (x * a ^ ((1 : ℝ) / 2)) ^ 2 = x ^ 2 * a := by
  rw [mul_pow, ← ENNReal.rpow_two (a ^ ((1 : ℝ) / 2)), ennreal_half_sq]

theorem ennreal_gain_factor_product (x y a : ℝ≥0∞) :
    (x * a ^ ((1 : ℝ) / 2)) * (y * a ^ ((1 : ℝ) / 2)) = x * y * a := by
  calc
    _ = (x * y) * (a ^ ((1 : ℝ) / 2) * a ^ ((1 : ℝ) / 2)) := by ac_rfl
    _ = _ := by rw [← pow_two, ← ENNReal.rpow_two, ennreal_half_sq]

theorem ennreal_ofReal_abs_sq (x : ℝ) : (ENNReal.ofReal |x|) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ENNReal.ofReal_pow (abs_nonneg x) 2, sq_abs]

end WaveTurbulence.WKEL2
