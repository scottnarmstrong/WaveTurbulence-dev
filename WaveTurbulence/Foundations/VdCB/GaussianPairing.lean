/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian regularization of the quadratic oscillatory integral

Fourier self-adjointness and the complex Gaussian transform give the
regularized quadratic identity. The real part is strictly positive here;
the oscillatory boundary limit is a separate theorem, not an assumption.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.VdCB

/-- The exact Gaussian pairing underlying one-dimensional stationary phase. -/
theorem integral_schwartz_mul_gaussian (a : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, a x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) =
      1 / b ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, 𝓕 a ξ * Complex.exp (-Real.pi / b * (ξ : ℂ) ^ 2) := by
  let G : ℝ → ℂ := fun x => Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)
  have hb' : 0 < ((Real.pi : ℂ) * b).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using mul_pos Real.pi_pos hb
  have hG : Integrable G := by
    simpa only [G, neg_mul, mul_assoc] using integrable_cexp_neg_mul_sq hb'
  have hh : (∫ ξ : ℝ, 𝓕 (𝓕⁻ a) ξ * G ξ) =
      ∫ x : ℝ, (𝓕⁻ a) x * 𝓕 G x := by
    have hraw := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner ((𝓕⁻ a).integrable (μ := volume)) hG
    simp only [flip_innerₗ, ContinuousLinearMap.mul_apply'] at hraw
    change (∫ ξ : ℝ, 𝓕 ((𝓕⁻ a : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ * G ξ) =
      ∫ x : ℝ, (𝓕⁻ a) x * 𝓕 G x at hraw
    simpa only [← SchwartzMap.fourier_coe] using hraw
  rw [FourierTransform.fourier_fourierInv_eq] at hh
  have hFG : 𝓕 G = fun x : ℝ => 1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (x : ℂ) ^ 2) := by
    simpa only [G] using fourier_gaussian_pi hb
  rw [hFG] at hh
  calc
    _ = ∫ x : ℝ, (𝓕⁻ a) x *
        (1 / b ^ (1 / 2 : ℂ) * Complex.exp (-Real.pi / b * (x : ℂ) ^ 2)) := hh
    _ = 1 / b ^ (1 / 2 : ℂ) *
        ∫ x : ℝ, 𝓕 (a : ℝ → ℂ) (-x) * Complex.exp (-Real.pi / b * (x : ℂ) ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
      ring
    _ = _ := by
      congr 1
      rw [← integral_neg_eq_self (fun x : ℝ => 𝓕 (a : ℝ → ℂ) (-x) *
        Complex.exp (-Real.pi / b * (x : ℂ) ^ 2))]
      simp only [neg_neg, Complex.ofReal_neg, neg_sq, SchwartzMap.fourier_coe]

end WaveTurbulence.VdCB
