/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelL1Bounds
import Mathlib.Tactic

/-!
# Fourier identities for cutoff Duhamel modes

The frequency-subtracted derivative corresponds exactly to the difference
between output and input frequencies. All identities include zero frequencies.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Fourier

/-- Fourier subtraction for integrable complex functions on the real line. -/
theorem fourier_sub_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : ℝ) : 𝓕 (f - g) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, Pi.sub_apply, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).mpr hf)
    ((Real.fourierIntegral_convergent_iff ξ).mpr hg)

/-- The output derivative supplies the output-frequency Fourier moment. -/
theorem fourier_deriv_duhamelMode {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ ξ : ℝ) :
    𝓕 (deriv (duhamelMode χ σ)) ξ =
      (2 * Real.pi * Complex.I * (ξ : ℂ)) * duhamelKernel χ ξ σ := by
  have hd := duhamelMode_contDiff hχ σ
  have hs := duhamelMode_hasCompactSupport hc σ
  exact congrFun (Real.fourier_deriv
    (hd.continuous.integrable_of_hasCompactSupport hs) (hd.differentiable (by simp))
    ((hd.continuous_deriv (by simp)).integrable_of_hasCompactSupport hs.deriv)) ξ

/-- The remainder supplies the difference-frequency Fourier moment. -/
theorem fourier_duhamelRemainder {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ ξ : ℝ) :
    𝓕 (duhamelRemainder χ σ) ξ =
      (2 * Real.pi * Complex.I * ((ξ - σ : ℝ) : ℂ)) * duhamelKernel χ ξ σ := by
  have hd := duhamelMode_contDiff hχ σ
  have hs := duhamelMode_hasCompactSupport hc σ
  have hi : Integrable (duhamelMode χ σ) := hd.continuous.integrable_of_hasCompactSupport hs
  have hdi : Integrable (deriv (duhamelMode χ σ)) :=
    (hd.continuous_deriv (by simp)).integrable_of_hasCompactSupport hs.deriv
  have hr : duhamelRemainder χ σ = deriv (duhamelMode χ σ) -
      (2 * Real.pi * Complex.I * (σ : ℂ)) • duhamelMode χ σ := by
    funext t
    exact duhamelRemainder_eq hχ σ t
  have hm : 𝓕 ((2 * Real.pi * Complex.I * (σ : ℂ)) • duhamelMode χ σ) ξ =
      (2 * Real.pi * Complex.I * (σ : ℂ)) * duhamelKernel χ ξ σ := by
    exact congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
      (innerₗ ℝ) (duhamelMode χ σ) (2 * Real.pi * Complex.I * (σ : ℂ))) ξ
  rw [hr, fourier_sub_integrable hdi (hi.smul (2 * Real.pi * Complex.I * (σ : ℂ))), hm,
    fourier_deriv_duhamelMode hχ hc]
  push_cast
  ring

/-- Differentiating the remainder supplies the joint Fourier moment. -/
theorem fourier_deriv_duhamelRemainder {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ ξ : ℝ) :
    𝓕 (deriv (duhamelRemainder χ σ)) ξ =
      (2 * Real.pi * Complex.I * (ξ : ℂ)) *
      ((2 * Real.pi * Complex.I * ((ξ - σ : ℝ) : ℂ)) * duhamelKernel χ ξ σ) := by
  have hd := duhamelRemainder_contDiff hχ σ
  have hs := duhamelRemainder_hasCompactSupport hc σ
  have h := congrFun (Real.fourier_deriv
    (hd.continuous.integrable_of_hasCompactSupport hs) (hd.differentiable (by simp))
    ((hd.continuous_deriv (by simp)).integrable_of_hasCompactSupport hs.deriv)) ξ
  simpa only [smul_eq_mul, fourier_duhamelRemainder hχ hc] using h

end WaveTurbulence.Fourier
