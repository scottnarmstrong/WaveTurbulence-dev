/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
# Uniform control data for a smooth compact cutoff

The time-integral estimates use only a support radius and bounds for the
first two cutoff derivatives. Every smooth compact cutoff supplies these
data; they are not additional assumptions on the source operators.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Elementary support and derivative bounds for a scalar cutoff. -/
structure CutoffControl (χ : ℝ → ℝ) where
  radius : ℝ
  bound : ℝ
  one_le_radius : 1 ≤ radius
  one_le_bound : 1 ≤ bound
  eq_zero : ∀ t, radius < |t| → χ t = 0
  abs_le : ∀ t, |χ t| ≤ bound
  abs_deriv_le : ∀ t, |deriv χ t| ≤ bound
  abs_second_deriv_le : ∀ t, |deriv (deriv χ) t| ≤ bound

/-- Continuous compactly supported scalar functions have a positive uniform bound. -/
theorem exists_positive_bound_of_continuous_compact {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hf).exists_bound_of_continuousOn continuousOn_id
  refine ⟨max 1 C, le_max_left _ _, fun t => ?_⟩
  have hh : |f t| ≤ C := by simpa only [Real.norm_eq_abs, id_eq] using hC (f t) ⟨t, rfl⟩
  exact hh.trans (le_max_right _ _)

/-- The support radius and all three derivative bounds exist for every source cutoff. -/
theorem exists_cutoffControl {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : Nonempty (CutoffControl χ) := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨C₀, hC₀, hb₀⟩ := exists_positive_bound_of_continuous_compact hχ.continuous hc
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hχ'' : ContDiff ℝ ∞ (deriv (deriv χ)) := (contDiff_infty_iff_deriv.mp hχ').2
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_positive_bound_of_continuous_compact hχ'.continuous hc.deriv
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_positive_bound_of_continuous_compact hχ''.continuous hc.deriv.deriv
  refine ⟨⟨max 1 R, C₀ + C₁ + C₂, le_max_left _ _, by linarith, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    by_contra hn
    have hm : t ∈ tsupport χ := subset_tsupport χ (by simpa using hn)
    have hh : |t| ≤ R := by simpa only [Real.norm_eq_abs, id_eq] using hR t hm
    exact (not_lt_of_ge (hh.trans (le_max_right _ _))) ht
  · intro t; linarith [hb₀ t]
  · intro t; linarith [hb₁ t]
  · intro t; linarith [hb₂ t]

end WaveTurbulence.Fourier
