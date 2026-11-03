/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NormalizedTail
public import WaveTurbulence.Foundations.VdCB.PoissonShiftedLimit

/-!
# Sharp truncated Poisson summation on a normalized derivative range

This is the integer-endpoint, unit-margin version of the van der Corput
truncation lemma (Titchmarsh, Lemma 4.7). The derivative is increasing and
lies in `[0,N]`; conjugation supplies the decreasing convention. The error
is explicit and independent of the spatial interval length.
-/

public section

open MeasureTheory Set Filter
open WaveTurbulence.NumberTheory
open scoped Topology

namespace WaveTurbulence.VdCB

/-- Sharp midpoint truncated Poisson estimate, with an explicit logarithmic
error and no assumed convergence of an absolute frequency sum. -/
theorem norm_midpoint_sum_sub_truncated_poisson_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        (expPhase (f b) - expPhase (f a)) / 2) -
      ∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
      (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hlim := (poisson_shifted_limit hf1 hab N).sub_const
    (∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x))
  have hout : Tendsto (fun K : ℕ => ∑ ν ∈ outerFrequencies N K,
      ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) atTop
      (𝓝 (((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        (expPhase (f b) - expPhase (f a)) / 2) -
      ∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x))) := by
    simpa only [sum_shifted_frequency_interval, add_sub_cancel_left] using hlim
  apply le_of_tendsto hout.norm
  apply Filter.Eventually.of_forall
  intro K
  simpa only [Int.cast_natCast] using norm_sum_outerFrequencies_integral_le hf
    (a : ℤ) (b : ℤ) (by exact_mod_cast hab) N K
    (by simpa only [Int.cast_natCast] using hrange)
    (by simpa only [Int.cast_natCast] using hsecond)

/-- The half-open sharp sum differs from the truncated integrals by a
logarithmic error plus one for the two endpoint half weights. -/
theorem norm_sum_sub_truncated_poisson_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) (N : ℕ)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
      (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1 := by
  have hmain := norm_midpoint_sum_sub_truncated_poisson_le hf hab N hrange hsecond
  have hend : ‖(expPhase (f b) - expPhase (f a)) / 2‖ ≤ 1 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hh := norm_sub_le (expPhase (f b)) (expPhase (f a))
    rw [norm_expPhase, norm_expPhase] at hh
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith only [hh])
  have heq : (∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      (∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) =
      (((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
        (expPhase (f b) - expPhase (f a)) / 2) -
      ∑ ν ∈ Finset.Icc 0 (N : ℤ), ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) +
        (expPhase (f b) - expPhase (f a)) / 2 := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hmain hend)

end WaveTurbulence.VdCB
