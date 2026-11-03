/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffPrimitive

/-!
# Uniform bounds for cutoff primitives at bounded frequencies

The estimates are uniform for lower endpoint `a ∈ [0,1]` and `|q| ≤ 1`.
They will be inserted into the quadratic Fourier-decay estimate.
-/

public section

open Set
open scoped ContDiff

namespace WaveTurbulence.Analysis

private theorem norm_timePrimitive_le_one_add_abs {a : ℝ} (ha : a ∈ Icc 0 1) (q t : ℝ) :
    ‖timePrimitive a q t‖ ≤ |t| + 1 := by
  have haabs : |a| ≤ 1 := by rw [abs_of_nonneg ha.1]; exact ha.2
  have hh := norm_sub_le t a
  simp only [Real.norm_eq_abs] at hh
  exact (norm_timePrimitive_le a q t).trans (hh.trans (add_le_add le_rfl haabs))

/-- Zeroth-order uniform bound. -/
theorem norm_cutoffPrimitive_le (χ : ℝ → ℂ) {a : ℝ} (ha : a ∈ Icc 0 1) (q t : ℝ) :
    ‖cutoffPrimitive χ a q t‖ ≤ ‖χ t‖ * (|t| + 1) := by
  rw [cutoffPrimitive, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_timePrimitive_le_one_add_abs ha q t) (norm_nonneg _)

private theorem norm_phase_deriv_coeff_le {q : ℝ} (hq : |q| ≤ 1) :
    ‖(2 * Real.pi * q : ℂ) * Complex.I‖ ≤ 2 * Real.pi := by
  have he : ‖(2 * Real.pi * q : ℂ) * Complex.I‖ = 2 * Real.pi * |q| := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [he]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * Real.pi)

/-- Uniform second-derivative bound at bounded frequency. -/
theorem norm_deriv_deriv_cutoffPrimitive_le {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {a q : ℝ} (ha : a ∈ Icc 0 1) (hq : |q| ≤ 1) (t : ℝ) :
    ‖deriv (deriv (cutoffPrimitive χ a q)) t‖ ≤
      ‖deriv (deriv χ) t‖ * (|t| + 1) + 2 * ‖deriv χ t‖ + 2 * Real.pi * ‖χ t‖ := by
  rw [deriv_deriv_cutoffPrimitive hχ]
  have hn :
      ‖deriv (deriv χ) t * timePrimitive a q t + 2 * deriv χ t * timePhase q t +
        χ t * ((2 * Real.pi * q : ℂ) * Complex.I) * timePhase q t‖ ≤
      ‖deriv (deriv χ) t * timePrimitive a q t‖ + ‖2 * deriv χ t * timePhase q t‖ +
        ‖χ t * ((2 * Real.pi * q : ℂ) * Complex.I) * timePhase q t‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have he : ‖2 * deriv χ t * timePhase q t‖ = 2 * ‖deriv χ t‖ := by
    rw [norm_mul, norm_mul, norm_timePhase, mul_one]
    norm_num
  rw [he] at hn
  simp only [norm_mul, norm_timePhase, mul_one] at hn
  have h1 := mul_le_mul_of_nonneg_left (norm_timePrimitive_le_one_add_abs ha q t)
    (norm_nonneg (deriv (deriv χ) t))
  have h2 := mul_le_mul_of_nonneg_left (norm_phase_deriv_coeff_le hq) (norm_nonneg (χ t))
  simp only [norm_mul] at h2
  calc
    _ ≤ _ := hn
    _ ≤ _ := by nlinarith only [h1, h2]

end WaveTurbulence.Analysis
