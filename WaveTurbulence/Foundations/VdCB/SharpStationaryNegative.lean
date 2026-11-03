/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SharpStationary
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Negative-curvature sharp stationary phase

Complex conjugation supplies the circle-arc convention. The quarter
phase is `-1/8`, and the positive weight is the square root of `-f''`.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The sharp stationary-phase estimate for a negative second derivative. -/
theorem norm_integral_stationary_neg_sub_main_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b c r μ M : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    (ha : a ≤ c - r) (hb : c + r ≤ b) (hc : deriv f c = 0)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv f) x ≤ -μ) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∫ x in a..b, expPhase (f x)) -
      expPhase (f c - 1 / 8) / (Real.sqrt (-deriv (deriv f) c) : ℂ)‖ ≤
      2 * Real.pi / 3 * M * r ^ 4 + 2 / (Real.pi * ((-deriv (deriv f) c) * r)) +
        2 / (Real.pi * (μ * r)) := by
  have hh := norm_integral_stationary_sub_main_le (f := fun x => -f x) hf.neg hr hμ ha hb
    (by simp only [deriv.fun_neg, hc, neg_zero])
    (by
      intro x hx
      simp only [deriv.fun_neg', deriv.fun_neg]
      linarith only [hcurv x hx]) hM0
    (by simpa only [iteratedDeriv_fun_neg, abs_neg] using hM)
  simp only [deriv.fun_neg', deriv.fun_neg] at hh
  have heq : (starRingEnd ℂ)
      ((∫ x in a..b, expPhase (-f x)) -
        expPhase (-f c + 1 / 8) / (Real.sqrt (-deriv (deriv f) c) : ℂ)) =
      (∫ x in a..b, expPhase (f x)) -
        expPhase (f c - 1 / 8) / (Real.sqrt (-deriv (deriv f) c) : ℂ) := by
    rw [map_sub, map_div₀, Complex.conj_ofReal]
    have hi : (starRingEnd ℂ) (∫ x in a..b, expPhase (-f x)) =
        ∫ x in a..b, expPhase (f x) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      simp only [conj_expPhase, neg_neg]
    rw [hi, conj_expPhase, show -(-f c + 1 / 8) = f c - 1 / 8 by ring]
  rw [← heq, Complex.norm_conj]
  exact hh

end WaveTurbulence.VdCB
