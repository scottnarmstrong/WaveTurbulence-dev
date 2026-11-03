/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffKernelIntegrability
public import WaveTurbulence.Foundations.Analysis.FrequencyWeights

/-! # Uniform mass bounds for the cutoff time kernel -/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Analysis

theorem cutoffKernelConstant_nonneg (χ : ℝ → ℂ) : 0 ≤ cutoffKernelConstant χ := by
  have h1 := cutoffSmallFrequencyConstant_nonneg χ
  have h2 := cutoffFourierConstant_nonneg χ
  unfold cutoffKernelConstant
  positivity

/-- The output-frequency `L¹` norm is uniformly bounded. -/
theorem integral_norm_cutoffTimeKernel_le {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (q : ℝ) :
    (∫ t : ℝ, ‖cutoffTimeKernel χ a t q‖) ≤ 2 * Real.pi * cutoffKernelConstant χ := by
  have hW := integrable_cauchyWeight
  have hb : Integrable (fun t : ℝ => cutoffKernelConstant χ * oscillatoryWeight q *
      (cauchyWeight t + cauchyWeight (t - q))) :=
    (hW.add (hW.comp_sub_right q)).const_mul _
  calc
    _ ≤ ∫ t : ℝ, cutoffKernelConstant χ * oscillatoryWeight q *
        (cauchyWeight t + cauchyWeight (t - q)) :=
      integral_mono (integrable_cutoffTimeKernel hχ hs ha q).norm hb
        (fun t => norm_cutoffTimeKernel_le hχ hs ha t q)
    _ = cutoffKernelConstant χ * oscillatoryWeight q * (Real.pi + Real.pi) := by
      rw [integral_const_mul, integral_add (f := cauchyWeight)
        (g := fun t : ℝ => cauchyWeight (t - q)) hW (hW.comp_sub_right q),
        integral_cauchyWeight, integral_cauchyWeight_sub]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (oscillatoryWeight_le_one q)
        (show 0 ≤ 2 * Real.pi * cutoffKernelConstant χ by
          exact mul_nonneg (by positivity) (cutoffKernelConstant_nonneg χ))
      nlinarith only [hh]

/-- The kernel is also bounded pointwise, uniformly in both frequencies. -/
theorem norm_cutoffTimeKernel_le_uniform {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (t q : ℝ) :
    ‖cutoffTimeKernel χ a t q‖ ≤ 2 * cutoffKernelConstant χ := by
  have hC := cutoffKernelConstant_nonneg χ
  calc
    _ ≤ _ := norm_cutoffTimeKernel_le hχ hs ha t q
    _ ≤ cutoffKernelConstant χ * 1 * (1 + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (oscillatoryWeight_le_one q) hC)
        (add_le_add (cauchyWeight_le_one t) (cauchyWeight_le_one (t - q)))
        (add_nonneg (cauchyWeight_pos t).le (cauchyWeight_pos (t - q)).le)
        (by simpa only [mul_one] using hC)
    _ = _ := by ring

end WaveTurbulence.Analysis
