/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.MeanInequalities

/-!
# Algebra of the Morrey scale

These identities isolate the real-power algebra from the potential estimate.
-/

public section

open scoped ENNReal

namespace WaveTurbulence.Analysis

theorem morrey_first_scale {r p q : ℝ} (hr : 0 < r) (hpq : p.HolderConjugate q) :
    (r ^ 2)⁻¹ * (r ^ 2) ^ (1 / q) = r ^ (-2 / p) := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_neg hr.le,
    ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1
  have hh := hpq.inv_add_inv_eq_one
  simp only [div_eq_mul_inv, one_mul, Nat.cast_ofNat] at *
  linarith only [hh]

theorem morrey_second_scale {r p q : ℝ} (hr : 0 < r) (hpq : p.HolderConjugate q) :
    (r ^ 2)⁻¹ * ((3 * r) ^ 2 / 2) * ((3 * r) ^ (2 - q)) ^ (1 / q) =
      ((9 / 2 : ℝ) * 3 ^ ((2 - q) * (1 / q))) * r ^ (1 - 2 / p) := by
  have hc : (r ^ 2)⁻¹ * ((3 * r) ^ 2 / 2) = (9 / 2 : ℝ) := by
    field_simp
    ring
  have he : (2 - q) * (1 / q) = 1 - 2 / p := by
    calc
      (2 - q) * (1 / q) = 2 * (1 / q) - 1 := by
        rw [sub_mul, mul_one_div_cancel hpq.symm.pos.ne']
      _ = _ := by
        have hh := hpq.inv_add_inv_eq_one
        simp only [div_eq_mul_inv, one_mul] at *
        linarith only [hh]
  rw [hc, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hr.le]
  rw [he]
  ring

/-- The same scale identities after passing to extended nonnegative reals.
The variables `A` and `B` are the two `Lᵖ` norms, and `I` is the geometric
kernel integral. This is a purely algebraic identity. -/
theorem morrey_scale_ennreal {r p q : ℝ} (hr : 0 < r) (hpq : p.HolderConjugate q)
    (A B I : ℝ≥0∞) :
    (ENNReal.ofReal r ^ 2)⁻¹ * (A * (ENNReal.ofReal r ^ 2) ^ (1 / q) +
      ENNReal.ofReal ((3 * r) ^ 2 / 2) *
        ((ENNReal.ofReal ((3 * r) ^ (2 - q)) * I) ^ (1 / q) * B)) =
      ENNReal.ofReal (r ^ (-2 / p)) * A +
        (ENNReal.ofReal ((9 / 2 : ℝ) * 3 ^ ((2 - q) * (1 / q))) * I ^ (1 / q)) *
          ENNReal.ofReal (r ^ (1 - 2 / p)) * B := by
  rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_rpow_of_pos (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpq.symm.nonneg),
    ENNReal.ofReal_rpow_of_pos (by positivity), mul_add]
  congr 1
  · calc
      ENNReal.ofReal ((r ^ 2)⁻¹) * (A * ENNReal.ofReal ((r ^ 2) ^ (1 / q))) =
          (ENNReal.ofReal ((r ^ 2)⁻¹) * ENNReal.ofReal ((r ^ 2) ^ (1 / q))) * A := by ring
      _ = ENNReal.ofReal ((r ^ 2)⁻¹ * (r ^ 2) ^ (1 / q)) * A := by
        rw [ENNReal.ofReal_mul (by positivity)]
      _ = _ := by rw [morrey_first_scale hr hpq]
  · calc
      ENNReal.ofReal ((r ^ 2)⁻¹) * (ENNReal.ofReal ((3 * r) ^ 2 / 2) *
          (ENNReal.ofReal (((3 * r) ^ (2 - q)) ^ (1 / q)) * I ^ (1 / q) * B)) =
          ((ENNReal.ofReal ((r ^ 2)⁻¹) * ENNReal.ofReal ((3 * r) ^ 2 / 2)) *
            ENNReal.ofReal (((3 * r) ^ (2 - q)) ^ (1 / q))) * I ^ (1 / q) * B := by ring
      _ = ENNReal.ofReal ((r ^ 2)⁻¹ * ((3 * r) ^ 2 / 2) *
          ((3 * r) ^ (2 - q)) ^ (1 / q)) * I ^ (1 / q) * B := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
        rw [morrey_second_scale hr hpq, ENNReal.ofReal_mul (by positivity)]
        ring

/-- Raising the first Morrey term to the exponent removes the `Lᵖ` root. -/
theorem morrey_power_first {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (A : ℝ≥0∞) :
    (ENNReal.ofReal (r ^ (-2 / p)) * A ^ (1 / p)) ^ p =
      ENNReal.ofReal (r ^ (-2 : ℝ)) * A := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ← Real.rpow_mul hr.le]
  congr 2
  field_simp

/-- Raising the gradient term to the exponent yields the power `r^{p-2}`. -/
theorem morrey_power_second {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (B C : ℝ≥0∞) :
    (C * ENNReal.ofReal (r ^ (1 - 2 / p)) * B ^ (1 / p)) ^ p =
      C ^ p * ENNReal.ofReal (r ^ (p - 2)) * B := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ← Real.rpow_mul hr.le]
  congr 3
  field_simp

end WaveTurbulence.Analysis
