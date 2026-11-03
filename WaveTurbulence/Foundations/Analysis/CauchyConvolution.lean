/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import WaveTurbulence.Foundations.Analysis.OscillatoryInterval

/-!
# Frequency envelopes for iterated time integrals

The quadratic Cauchy envelope is integrable and stable under convolution.
These bounds are used with the Fourier kernel of cutoff time integration.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- Integrable quadratic frequency envelope. -/
@[expose] noncomputable def cauchyWeight (x : ℝ) : ℝ := (1 + x ^ 2)⁻¹

theorem cauchyWeight_pos (x : ℝ) : 0 < cauchyWeight x := by
  unfold cauchyWeight
  positivity

/-- The pointwise inequality that makes the Cauchy envelope stable under
convolution. -/
theorem cauchyWeight_mul_le (x y : ℝ) :
    cauchyWeight (x - y) * cauchyWeight y ≤
      2 * cauchyWeight x * (cauchyWeight (x - y) + cauchyWeight y) := by
  have hA : 0 < 1 + (x - y) ^ 2 := by positivity
  have hB : 0 < 1 + y ^ 2 := by positivity
  have hC : 0 < 1 + x ^ 2 := by positivity
  unfold cauchyWeight
  apply (mul_le_mul_iff_right₀ hA).mp
  apply (mul_le_mul_iff_right₀ hB).mp
  apply (mul_le_mul_iff_right₀ hC).mp
  field_simp
  nlinarith only [sq_nonneg (x - 2 * y)]

/-- The mass of the quadratic envelope is `π`. -/
theorem lintegral_cauchyWeight :
    (∫⁻ y : ℝ, ENNReal.ofReal (cauchyWeight y)) = ENNReal.ofReal Real.pi := by
  change (∫⁻ y : ℝ, ENNReal.ofReal ((1 + y ^ 2)⁻¹)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
    (Filter.Eventually.of_forall fun x => (cauchyWeight_pos x).le), integral_univ_inv_one_add_sq]

/-- Convolution preserves the quadratic decay, with an explicit constant. -/
theorem lintegral_cauchyWeight_mul_le (x : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal (cauchyWeight (x - y)) * ENNReal.ofReal (cauchyWeight y)) ≤
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (cauchyWeight x) := by
  have hpoint (y : ℝ) :
      ENNReal.ofReal (cauchyWeight (x - y)) * ENNReal.ofReal (cauchyWeight y) ≤
        ENNReal.ofReal (2 * cauchyWeight x) *
          (ENNReal.ofReal (cauchyWeight (x - y)) + ENNReal.ofReal (cauchyWeight y)) := by
    have hh := ENNReal.ofReal_le_ofReal (cauchyWeight_mul_le x y)
    rw [ENNReal.ofReal_mul (cauchyWeight_pos (x - y)).le,
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) (cauchyWeight_pos x).le), ENNReal.ofReal_add
        (cauchyWeight_pos (x - y)).le (cauchyWeight_pos y).le] at hh
    exact hh
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (cauchyWeight (x - y))) := by
    unfold cauchyWeight
    fun_prop
  have hm0 : Measurable (fun y : ℝ => ENNReal.ofReal (cauchyWeight y)) := by
    unfold cauchyWeight
    fun_prop
  have hmsum : Measurable (fun y : ℝ => ENNReal.ofReal (cauchyWeight (x - y)) +
      ENNReal.ofReal (cauchyWeight y)) := by fun_prop
  calc
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2 * cauchyWeight x) *
        (ENNReal.ofReal (cauchyWeight (x - y)) + ENNReal.ofReal (cauchyWeight y)) :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul _ hmsum,
        lintegral_add_left hm, lintegral_sub_left_eq_self
          (fun y : ℝ => ENNReal.ofReal (cauchyWeight y)) x, lintegral_cauchyWeight]
      rw [← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (cauchyWeight_pos x).le), ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      congr 1
      ring

end WaveTurbulence.Analysis
