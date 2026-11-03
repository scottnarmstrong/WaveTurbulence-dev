/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SharpLocalStationary
public import WaveTurbulence.Foundations.VdCB.NonstationaryNegative
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Sharp stationary phase on a general interval

A positive lower bound on the actual second derivative controls both
nonstationary tails. The central cubic error and the Fresnel cutoff error
remain explicit, so the radius can be optimized by a consumer.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- A sharp C³ stationary-phase estimate with actual derivative bounds.
This radius-dependent form of the one-dimensional stationary-phase lemma
separates the cubic remainder, quadratic tail and outer tails. -/
theorem norm_integral_stationary_sub_main_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b c r μ M : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    (ha : a ≤ c - r) (hb : c + r ≤ b) (hc : deriv f c = 0)
    (hcurv : ∀ x ∈ Icc a b, μ ≤ deriv (deriv f) x) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∫ x in a..b, expPhase (f x)) -
      expPhase (f c + 1 / 8) / (Real.sqrt (deriv (deriv f) c) : ℂ)‖ ≤
      2 * Real.pi / 3 * M * r ^ 4 + 2 / (Real.pi * (deriv (deriv f) c * r)) +
        2 / (Real.pi * (μ * r)) := by
  have hcI : c ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hq : 0 < deriv (deriv f) c := hμ.trans_le (hcurv c hcI)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 (deriv f) := hf2.deriv'
  have hsec := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hf1.continuous.continuousOn (hf1.differentiable (by norm_num)).differentiableOn
    (fun x hx => hcurv x (interior_subset hx))
  have hl := norm_integral_expPhase_le_of_deriv_neg hf2 ha (mul_pos hμ hr)
    (fun x hx => by
      have hh := hsec x ⟨hx.1, by linarith [hx.2]⟩ c hcI (by linarith [hx.2])
      rw [hc] at hh
      nlinarith [mul_nonneg hμ.le (show 0 ≤ c - x - r by linarith [hx.2])])
    (fun x hx => hμ.le.trans (hcurv x ⟨hx.1, by linarith [hx.2]⟩))
  have hrgt := norm_integral_expPhase_le_of_deriv_pos hf2 hb (mul_pos hμ hr)
    (fun x hx => by
      have hh := hsec c hcI x ⟨by linarith [hx.1], hx.2⟩ (by linarith [hx.1])
      rw [hc, sub_zero] at hh
      nlinarith [mul_nonneg hμ.le (show 0 ≤ x - c - r by linarith [hx.1])])
    (fun x hx => hμ.le.trans (hcurv x ⟨by linarith [hx.1], hx.2⟩))
  have hloc := norm_integral_local_stationary_sub_main_le hf c hc hq hr hM0 hM
  have hcf : Continuous (fun x => expPhase (f x)) := (contDiff_expPhase 0).continuous.comp hf.continuous
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (μ := volume) a (c - r))
    (hcf.intervalIntegrable (μ := volume) (c - r) (c + r))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hcf.intervalIntegrable (μ := volume) a (c + r))
    (hcf.intervalIntegrable (μ := volume) (c + r) b)
  have heq : (∫ x in a..b, expPhase (f x)) -
      expPhase (f c + 1 / 8) / (Real.sqrt (deriv (deriv f) c) : ℂ) =
      ((∫ x in a..c - r, expPhase (f x)) +
       ((∫ x in c - r..c + r, expPhase (f x)) -
        expPhase (f c + 1 / 8) / (Real.sqrt (deriv (deriv f) c) : ℂ))) +
       ∫ x in c + r..b, expPhase (f x) := by
    rw [← h2, ← h1]
    ring
  rw [heq]
  calc
    _ ≤ (‖∫ x in a..c - r, expPhase (f x)‖ +
      ‖(∫ x in c - r..c + r, expPhase (f x)) -
        expPhase (f c + 1 / 8) / (Real.sqrt (deriv (deriv f) c) : ℂ)‖) +
      ‖∫ x in c + r..b, expPhase (f x)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 / (Real.pi * (μ * r)) +
      (2 * Real.pi / 3 * M * r ^ 4 + 2 / (Real.pi * (deriv (deriv f) c * r)))) +
      1 / (Real.pi * (μ * r)) := add_le_add (add_le_add hl hloc) hrgt
    _ = _ := by ring

end WaveTurbulence.VdCB
