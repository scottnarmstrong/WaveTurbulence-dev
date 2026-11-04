/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import WaveTurbulence.Foundations.Torus.Derivative
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Coordinate integration by parts for the product-space Fourier transform

Compact smooth amplitudes admit the coordinate derivative identity required
for the frequency tails in TARGET `lemcubic0`.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped ContDiff

/-- The continuous bilinear dot product on physical coordinates. -/
@[expose] noncomputable def coordinatePairing (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

@[simp] theorem coordinatePairing_apply {n : ℕ} (x y : Fin n → ℝ) :
    coordinatePairing n x y = ∑ i, x i * y i := by
  simp only [coordinatePairing, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.mul_apply']

theorem coordinatePairing_toLinearMap (n : ℕ) :
    (coordinatePairing n).toLinearMap₁₂ = Fourier.timePairing n := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact coordinatePairing_apply x y

/-- Fourier differentiation for compact smooth physical-coordinate functions. -/
theorem timeFourier_partialDeriv {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : Fin n) (ν : Fin n → ℝ) :
    Fourier.timeFourier (partialDeriv j f) ν =
      (2 * Real.pi * Complex.I * (ν j : ℂ)) * Fourier.timeFourier f ν := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hdi : Integrable (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).continuous.integrable_of_hasCompactSupport
      (hc.fderiv (𝕜 := ℝ))
  have he := congrArg (fun H => H ν (Pi.single j 1))
    (VectorFourier.fourierIntegral_fderiv (coordinatePairing n) hi hd hdi)
  rw [Real.fourierIntegral_continuousLinearMap_apply' hdi] at he
  rw [coordinatePairing_toLinearMap] at he
  rw [partialDeriv_eq_fderiv_fun hd j]
  have hs : (∑ i : Fin n, (Pi.single j (1 : ℝ) : Fin n → ℝ) i * ν i) = ν j := by
    simp [Pi.single_apply]
  simpa only [Fourier.timeFourier, VectorFourier.fourierSMulRight_apply, neg_apply,
    ContinuousLinearMap.flip_apply, coordinatePairing_apply, hs,
    one_mul, neg_smul, smul_neg, neg_neg, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_neg, mul_neg, neg_mul, mul_assoc] using he

end WaveTurbulence.LemLin
