/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Physical L¹–L∞ interpolation for the couple kernel

TARGET (incohproof18)–(incohproof20): the exponent `1+3η` in the landed
time-integral estimate costs only a small power of the pointwise bound.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The exact L¹–L∞ interpolation bound, retaining extended-valued constants. -/
theorem eLpNorm_le_of_one_and_pointwise {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℂ} (hF : AEStronglyMeasurable F μ) {p : ℝ} (hp : 1 ≤ p)
    {A B : ℝ≥0∞} (hA : eLpNorm F 1 μ ≤ A) (hB : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ B) :
    eLpNorm F (ENNReal.ofReal p) μ ≤ A ^ (1 / p) * B ^ (1 - 1 / p) := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hp₁ : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have H : (∫⁻ x, ‖F x‖ₑ ^ p ∂μ) ≤ B ^ (p - 1) * A := by
    calc
      _ ≤ ∫⁻ x, B ^ (p - 1) * ‖F x‖ₑ ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hB] with x hx
        have heq : ‖F x‖ₑ ^ p = ‖F x‖ₑ ^ (p - 1) * ‖F x‖ₑ := by
          simpa only [sub_add_cancel, ENNReal.rpow_one] using
            (ENNReal.rpow_add_of_nonneg (x := ‖F x‖ₑ) (p - 1) 1 hp₁ zero_le_one)
        rw [heq]
        exact mul_le_mul' (ENNReal.rpow_le_rpow hx hp₁) le_rfl
      _ = B ^ (p - 1) * ∫⁻ x, ‖F x‖ₑ ∂μ := lintegral_const_mul'' _ hF.enorm
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_enorm_le_eLpNorm_one.trans hA)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp₀).ne'
    ENNReal.ofReal_ne_top hF, ENNReal.toReal_ofReal hp₀.le]
  apply (ENNReal.rpow_le_rpow H (by positivity : 0 ≤ 1 / p)).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p), ← ENNReal.rpow_mul]
  have he : (p - 1) * (1 / p) = 1 - 1 / p := by field_simp
  rw [he, mul_comm]

/-- Scaled endpoint interpolation factors out the common L¹ scale exactly. -/
theorem eLpNorm_le_of_one_and_scaled_pointwise {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℂ} (hF : AEStronglyMeasurable F μ) {p : ℝ} (hp : 1 ≤ p)
    {A B : ℝ≥0∞} (hA : eLpNorm F 1 μ ≤ A) (hB : ∀ᵐ x ∂μ, ‖F x‖ₑ ≤ A * B) :
    eLpNorm F (ENNReal.ofReal p) μ ≤ A * B ^ (1 - 1 / p) := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have ha : 0 ≤ 1 / p := by positivity
  have hb : 0 ≤ 1 - 1 / p := sub_nonneg.mpr ((div_le_one hp₀).mpr hp)
  apply (eLpNorm_le_of_one_and_pointwise hF hp hA hB).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hb]
  calc
    _ = (A ^ (1 / p) * A ^ (1 - 1 / p)) * B ^ (1 - 1 / p) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / p) (1 - 1 / p) ha hb,
        add_sub_cancel, ENNReal.rpow_one]

end WaveTurbulence.Incoh
