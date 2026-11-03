/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffFourierFormula

/-!
# Uniform Fourier bound for cutoff time integration

The time kernel has two quadratic envelopes, centred at zero and at the
input frequency, and a reciprocal Japanese bracket in that frequency.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Analysis

/-- Quadratic Fourier-decay constant of the cutoff alone. -/
@[expose] noncomputable def cutoffFourierConstant (χ : ℝ → ℂ) : ℝ :=
  (∫ s : ℝ, ‖χ s‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ s : ℝ, ‖deriv (deriv χ) s‖

theorem cutoffFourierConstant_nonneg (χ : ℝ → ℂ) : 0 ≤ cutoffFourierConstant χ := by
  unfold cutoffFourierConstant
  positivity

/-- Quadratic Fourier decay of a smooth compactly supported cutoff. -/
theorem norm_fourier_cutoff_le {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (t : ℝ) : ‖𝓕 χ t‖ ≤ cutoffFourierConstant χ * cauchyWeight t := by
  have hi (k : ℕ) : Integrable (iteratedDeriv k χ) :=
    (hχ.continuous_iteratedDeriv k (by simp)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv hs k)
  have hh := Real.one_add_sq_mul_norm_fourier_le (hχ.of_le (by norm_num)) (fun k _ => hi k) t
  have heq : iteratedDeriv 2 χ = deriv (deriv χ) := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq] at hh
  rw [cauchyWeight, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr (by simpa only [cutoffFourierConstant, mul_comm] using hh)

private theorem one_le_four_weight {q : ℝ} (hq : |q| ≤ 1) : 1 ≤ 4 * oscillatoryWeight q := by
  have hs : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + q ^ 2 by positivity)
  have hsq : q ^ 2 ≤ 1 := by
    nlinarith only [sq_abs q, sq_le_sq₀ (abs_nonneg q) zero_le_one |>.mpr hq]
  have hsle : Real.sqrt (1 + q ^ 2) ≤ 4 := by nlinarith only [hs2, hs.le, hsq]
  rw [oscillatoryWeight, ← div_eq_mul_inv]
  exact (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsle)

private theorem inv_abs_le_two_weight {q : ℝ} (hq : 1 < |q|) :
    1 / |q| ≤ 2 * oscillatoryWeight q := by
  have hqpos : 0 < |q| := zero_lt_one.trans hq
  have hs : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + q ^ 2 by positivity)
  have hq1 : 1 ≤ q ^ 2 := by nlinarith only [sq_abs q, hq]
  have hsle : Real.sqrt (1 + q ^ 2) ≤ 2 * |q| := by
    nlinarith only [hs2, hs.le, hq1, sq_abs q, hqpos]
  rw [oscillatoryWeight, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hqpos hs).mpr
  simpa only [one_mul] using hsle

/-- A single constant for both frequency ranges, depending only on the cutoff. -/
@[expose] noncomputable def cutoffKernelConstant (χ : ℝ → ℂ) : ℝ :=
  4 * (cutoffSmallFrequencyConstant χ + cutoffFourierConstant χ + 1)

/-- Uniform Fourier estimate for cutoff time integration, with arbitrary
lower endpoint in the unit interval. -/
theorem norm_cutoffTimeKernel_le {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (t q : ℝ) :
    ‖cutoffTimeKernel χ a t q‖ ≤ cutoffKernelConstant χ * oscillatoryWeight q *
      (cauchyWeight t + cauchyWeight (t - q)) := by
  have hS := cutoffSmallFrequencyConstant_nonneg χ
  have hF := cutoffFourierConstant_nonneg χ
  have hC : 0 ≤ cutoffKernelConstant χ := by unfold cutoffKernelConstant; positivity
  have hJ : 0 ≤ oscillatoryWeight q := by unfold oscillatoryWeight; positivity
  have hW : 0 ≤ cauchyWeight t := (cauchyWeight_pos t).le
  have hV : 0 ≤ cauchyWeight (t - q) := (cauchyWeight_pos (t - q)).le
  by_cases hq : |q| ≤ 1
  · have hc : 4 * cutoffSmallFrequencyConstant χ ≤ cutoffKernelConstant χ := by
      unfold cutoffKernelConstant
      linarith only [hF]
    calc
      _ ≤ cutoffSmallFrequencyConstant χ * cauchyWeight t :=
        norm_cutoffTimeKernel_le_of_abs_le_one hχ hs ha hq t
      _ ≤ (4 * cutoffSmallFrequencyConstant χ) * oscillatoryWeight q * cauchyWeight t := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (one_le_four_weight hq) hS) hW
        nlinarith only [hh]
      _ ≤ cutoffKernelConstant χ * oscillatoryWeight q * cauchyWeight t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hJ) hW
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hV) (mul_nonneg hC hJ)
  · have hq1 : 1 < |q| := lt_of_not_ge hq
    have hqpos : 0 < |q| := zero_lt_one.trans hq1
    have hq0 : q ≠ 0 := abs_pos.mp hqpos
    have hi := hχ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
    have hden : ‖(2 * Real.pi * q : ℂ) * Complex.I‖ = 2 * Real.pi * |q| := by
      norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hnum : ‖𝓕 χ (t - q) - timePhase q a * 𝓕 χ t‖ ≤
        cutoffFourierConstant χ * (cauchyWeight (t - q) + cauchyWeight t) := by
      calc
        _ ≤ ‖𝓕 χ (t - q)‖ + ‖timePhase q a * 𝓕 χ t‖ := norm_sub_le _ _
        _ = ‖𝓕 χ (t - q)‖ + ‖𝓕 χ t‖ := by rw [norm_mul, norm_timePhase, one_mul]
        _ ≤ _ := by
          have h1 := norm_fourier_cutoff_le hχ hs (t - q)
          have h2 := norm_fourier_cutoff_le hχ hs t
          nlinarith only [h1, h2]
    have hpi : 1 ≤ 2 * Real.pi := by have hh := Real.two_le_pi; linarith only [hh]
    have hdenle : |q| ≤ 2 * Real.pi * |q| :=
      le_mul_of_one_le_left (abs_nonneg q) hpi
    have hc : 2 * cutoffFourierConstant χ ≤ cutoffKernelConstant χ := by
      unfold cutoffKernelConstant
      linarith only [hS, hF]
    calc
      _ = ‖𝓕 χ (t - q) - timePhase q a * 𝓕 χ t‖ / (2 * Real.pi * |q|) := by
        rw [cutoffTimeKernel_eq_of_ne_zero hi a t q hq0, norm_div, hden]
      _ ≤ (cutoffFourierConstant χ * (cauchyWeight (t - q) + cauchyWeight t)) /
          (2 * Real.pi * |q|) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (cutoffFourierConstant χ * (cauchyWeight (t - q) + cauchyWeight t)) / |q| :=
        div_le_div_of_nonneg_left (mul_nonneg hF (add_nonneg hV hW)) hqpos hdenle
      _ = (cutoffFourierConstant χ * (1 / |q|)) * (cauchyWeight (t - q) + cauchyWeight t) := by ring
      _ ≤ (2 * cutoffFourierConstant χ) * oscillatoryWeight q *
          (cauchyWeight (t - q) + cauchyWeight t) := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (inv_abs_le_two_weight hq1) hF) (add_nonneg hV hW)
        nlinarith only [hh]
      _ ≤ cutoffKernelConstant χ * oscillatoryWeight q *
          (cauchyWeight (t - q) + cauchyWeight t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hJ) (add_nonneg hV hW)
      _ = _ := by rw [add_comm]

end WaveTurbulence.Analysis
