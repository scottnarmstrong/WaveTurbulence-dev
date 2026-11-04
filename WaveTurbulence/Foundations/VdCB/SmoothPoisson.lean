/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Exact smooth Poisson summation for exponential sums

The compact amplitude is retained in both the sum and the integral.
Removing it at sharp endpoints and truncating the dual frequencies require
the separate harmonic-tail estimates; neither error is hidden here.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- A compact smooth amplitude times the actual oscillatory phase. -/
@[expose] noncomputable def phaseSchwartz {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    (hs : HasCompactSupport A) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : 𝓢(ℝ, ℂ) :=
  (hs.mul_right (f' := fun x => expPhase (f x))).toSchwartzMap
    (hA.mul ((contDiff_expPhase ∞).comp hf))

/-- Fourier coefficients in the same phase convention as the finite sum. -/
theorem fourier_amplitude_expPhase (A : ℝ → ℂ) (f : ℝ → ℝ) (ν : ℝ) :
    𝓕 (fun x => A x * expPhase (f x)) ν =
      ∫ x : ℝ, A x * expPhase (f x - ν * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  have hp : Complex.exp ((-2 * Real.pi * x * ν : ℝ) * Complex.I) = expPhase (-ν * x) := by
    unfold expPhase
    congr 1
    push_cast
    ring
  rw [hp, smul_eq_mul, ← mul_assoc, mul_comm (expPhase (-ν * x)) (A x), mul_assoc,
    ← expPhase_add, show -ν * x + f x = f x - ν * x by ring]

/-- Exact Poisson summation with an actual smooth compact amplitude. -/
theorem poisson_amplitude_expPhase {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    (hs : HasCompactSupport A) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    (∑' n : ℤ, A n * expPhase (f n)) =
      ∑' ν : ℤ, ∫ x : ℝ, A x * expPhase (f x - (ν : ℝ) * x) := by
  have hh := (phaseSchwartz hA hs hf).tsum_eq_tsum_fourier 0
  simp only [zero_add, AddCircle.coe_zero, fourier_eval_zero, mul_one,
    SchwartzMap.fourier_coe] at hh
  change (∑' n : ℤ, A n * expPhase (f n)) = ∑' ν : ℤ, 𝓕 (fun x => A x * expPhase (f x)) ν at hh
  simpa only [fourier_amplitude_expPhase] using hh

end WaveTurbulence.VdCB
