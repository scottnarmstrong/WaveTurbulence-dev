/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PoissonMarginShift

/-!
# Sharp truncated Poisson for decreasing phase derivatives

Conjugation supplies the source convention `α≤f'≤β`, `f''≤0`. Modes are
written as `-(m+ν)` after integer normalization of the negated derivative.
The adjustable cutoff is exactly the usual open derivative-range window.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Adjustable-margin sharp Poisson in the decreasing-derivative convention.
The original source sum and the actual original oscillatory integrals occur
in the conclusion. No phase transformation is left as an analytic premise. -/
theorem norm_sum_sub_truncated_poisson_margin_neg_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) {α β η : ℝ} (m : ℤ) (N : ℕ)
    (hα0 : (m : ℝ) ≤ -β) (hα1 : -β < m + 1)
    (hβ0 : (m : ℝ) + N - 1 < -α) (hβN : -α ≤ m + N) (hη : 0 < η)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, α ≤ deriv f x ∧ deriv f x ≤ β)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, deriv (deriv f) x ≤ 0) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ marginFrequencies (-β - m) (-α - m) η N,
        ∫ x in (a : ℝ)..b, expPhase (f x + ((m : ℝ) + ν) * x)‖ ≤
      ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        2 / (Real.pi * η) := by
  have hh := norm_sum_sub_truncated_poisson_margin_shift_le (f := fun x => -f x) hf.neg hab m N
    hα0 hα1 hβ0 hβN hη
    (by
      intro x hx
      rw [deriv.fun_neg]
      obtain ⟨h1, h2⟩ := hrange x hx
      constructor <;> linarith only [h1, h2])
    (by
      intro x hx
      rw [deriv.fun_neg', deriv.fun_neg]
      exact neg_nonneg.mpr (hsecond x hx))
  have hsource : (starRingEnd ℂ) (∑ n ∈ Finset.Ico a b, expPhase (-f ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [conj_expPhase, neg_neg]
  have hI (ν : ℤ) : (starRingEnd ℂ)
      (∫ x in (a : ℝ)..b, expPhase (-f x - ((m : ℝ) + ν) * x)) =
        ∫ x in (a : ℝ)..b, expPhase (f x + ((m : ℝ) + ν) * x) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [conj_expPhase]
    congr 1
    ring
  have heq : (starRingEnd ℂ)
      ((∑ n ∈ Finset.Ico a b, expPhase (-f ((n : ℝ) + 1))) -
       ∑ ν ∈ marginFrequencies (-β - m) (-α - m) η N,
         ∫ x in (a : ℝ)..b, expPhase (-f x - ((m : ℝ) + ν) * x)) =
      ((∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
       ∑ ν ∈ marginFrequencies (-β - m) (-α - m) η N,
         ∫ x in (a : ℝ)..b, expPhase (f x + ((m : ℝ) + ν) * x)) := by
    rw [map_sub, hsource, map_sum]
    simp_rw [hI]
  rw [← heq, Complex.norm_conj]
  exact hh

end WaveTurbulence.VdCB
