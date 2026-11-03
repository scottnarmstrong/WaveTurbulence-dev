/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeBasic
public import WaveTurbulence.Foundations.Torus.Derivative
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic

/-!
# Coordinate derivatives and time Fourier moments

The coordinate partial derivative is the author-frozen `partialDeriv`.
Integration by parts converts it into multiplication by `2π i ξ_j`.
These identities underlie the time-integral estimates in TARGET A.2–A.3.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The coordinate time pairing as a continuous bilinear map. -/
@[expose] noncomputable def timePairingCLM (r : ℕ) :
    (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (ContinuousLinearMap.proj j)

@[simp] theorem timePairingCLM_apply {r : ℕ} (x ξ : Fin r → ℝ) :
    timePairingCLM r x ξ = timePairing r x ξ := by
  simp only [timePairingCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  rfl

@[simp] theorem timePairingCLM_toLinearMap (r : ℕ) :
    (timePairingCLM r).toLinearMap₁₂ = timePairing r := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro ξ
  exact timePairingCLM_apply x ξ

/-- A directional time derivative becomes a linear Fourier multiplier. -/
theorem timeFourier_fderiv_apply {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hd : Differentiable ℝ f) (hdf : Integrable (fderiv ℝ f))
    (v ξ : Fin r → ℝ) :
    timeFourier (fun x => fderiv ℝ f x v) ξ =
      (2 * Real.pi * Complex.I * (timePairing r v ξ : ℂ)) * timeFourier f ξ := by
  have h := congrArg (fun G : (Fin r → ℝ) → ((Fin r → ℝ) →L[ℝ] ℂ) => G ξ v)
    (VectorFourier.fourierIntegral_fderiv (L := timePairingCLM r) hf hd hdf)
  rw [Real.fourierIntegral_continuousLinearMap_apply' hdf] at h
  simpa only [timePairingCLM_toLinearMap, VectorFourier.fourierSMulRight_apply,
    neg_apply, ContinuousLinearMap.flip_apply, timePairingCLM_apply,
    neg_smul, smul_neg, neg_neg, Complex.real_smul, smul_eq_mul, mul_assoc,
    mul_neg, neg_mul, timeFourier] using h

/-- Fourier multiplier for the frozen coordinate partial derivative. -/
theorem timeFourier_partialDeriv {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hd : Differentiable ℝ f) (hdf : Integrable (fderiv ℝ f))
    (j : Fin r) (ξ : Fin r → ℝ) :
    timeFourier (WaveTurbulence.partialDeriv j f) ξ =
      (2 * Real.pi * Complex.I * (ξ j : ℂ)) * timeFourier f ξ := by
  rw [WaveTurbulence.partialDeriv_eq_fderiv_fun hd j]
  have h := timeFourier_fderiv_apply hf hd hdf (Pi.single j 1) ξ
  simpa [timePairing, dotProduct, Pi.single_apply] using h

/-- Coordinate partial derivatives of a differentiable compactly supported function
remain compactly supported. -/
theorem hasCompactSupport_partialDeriv {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hd : Differentiable ℝ f) (hc : HasCompactSupport f) (j : Fin r) :
    HasCompactSupport (WaveTurbulence.partialDeriv j f) := by
  rw [WaveTurbulence.partialDeriv_eq_fderiv_fun hd j]
  exact hc.fderiv_apply ℝ (Pi.single j 1)

/-- Compact smooth functions need no separate integrability assumptions
for the derivative Fourier identity. -/
theorem timeFourier_partialDeriv_smooth_compact {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : Fin r) (ξ : Fin r → ℝ) :
    timeFourier (WaveTurbulence.partialDeriv j f) ξ =
      (2 * Real.pi * Complex.I * (ξ j : ℂ)) * timeFourier f ξ :=
  timeFourier_partialDeriv (hf.continuous.integrable_of_hasCompactSupport hc)
    (hf.differentiable (by simp))
    ((hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hc.fderiv ℝ)) j ξ

end WaveTurbulence.Fourier
