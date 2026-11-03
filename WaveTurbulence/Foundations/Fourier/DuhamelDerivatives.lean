/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelModes
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
# Integration by parts for cutoff Duhamel modes

DNY21 Lemma 3.1, TARGET L2365–L2368. Subtracting the input-frequency
multiple of the output derivative exposes primitives of cutoff derivatives.
Those primitives are uniformly bounded, including at input frequency zero.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Differentiating an input Fourier mode gives its `2π i σ` multiplier. -/
theorem hasDerivAt_duhamelPhase (σ t : ℝ) :
    HasDerivAt (fun u : ℝ => (Real.fourierChar (σ * u) : ℂ))
      ((2 * Real.pi * Complex.I * (σ : ℂ)) * (Real.fourierChar (σ * t) : ℂ)) t := by
  have h := (Real.hasDerivAt_fourierChar (σ * t)).scomp t ((hasDerivAt_id t).const_mul σ)
  simpa only [Function.comp_def, id_eq, mul_one, Complex.real_smul, mul_assoc,
    mul_left_comm, mul_comm] using h

/-- Product-rule derivative of a cutoff input mode. -/
theorem hasDerivAt_cutoffPhase {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (σ t : ℝ) :
    HasDerivAt (fun u : ℝ => (χ u : ℂ) * (Real.fourierChar (σ * u) : ℂ))
      (((deriv χ t : ℝ) : ℂ) * (Real.fourierChar (σ * t) : ℂ) +
        (2 * Real.pi * Complex.I * (σ : ℂ)) *
          ((χ t : ℂ) * (Real.fourierChar (σ * t) : ℂ))) t := by
  convert ((hχ t).hasDerivAt.ofReal_comp).mul (hasDerivAt_duhamelPhase σ t) using 1
  ring

/-- Integration by parts of the cutoff primitive; no division by `σ` is used. -/
theorem duhamelPrimitive_frequency_identity {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (σ t : ℝ) :
    (2 * Real.pi * Complex.I * (σ : ℂ)) * duhamelPrimitive χ σ t =
      (χ t : ℂ) * (Real.fourierChar (σ * t) : ℂ) - (χ 0 : ℂ) -
        duhamelPrimitive (deriv χ) σ t := by
  let E := fun u : ℝ => (Real.fourierChar (σ * u) : ℂ)
  let z : ℂ := 2 * Real.pi * Complex.I * (σ : ℂ)
  have hEd : Differentiable ℝ E := fun u => (hasDerivAt_duhamelPhase σ u).differentiableAt
  have hE : Continuous E := hEd.continuous
  have hc : Continuous (fun u => (χ u : ℂ) * E u) :=
    (Complex.continuous_ofReal.comp hχ.continuous).mul hE
  have hc' : Continuous (fun u => ((deriv χ u : ℝ) : ℂ) * E u) :=
    (Complex.continuous_ofReal.comp (hχ.continuous_deriv (by simp))).mul hE
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_cutoffPhase (hχ.differentiable (by simp)) σ u)
    ((hc'.add (hc.const_mul z)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_add (hc'.intervalIntegrable 0 t)
    ((hc.const_mul z).intervalIntegrable 0 t), intervalIntegral.integral_const_mul] at h
  change duhamelPrimitive (deriv χ) σ t + z * duhamelPrimitive χ σ t =
    (χ t : ℂ) * E t - (χ 0 : ℂ) * E 0 at h
  have hE0 : E 0 = 1 := by simp [E]
  rw [hE0, mul_one] at h
  change z * duhamelPrimitive χ σ t = (χ t : ℂ) * E t - (χ 0 : ℂ) -
    duhamelPrimitive (deriv χ) σ t
  linear_combination h

/-- Derivative of the cutoff output mode. -/
theorem hasDerivAt_duhamelMode {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (σ t : ℝ) :
    HasDerivAt (duhamelMode χ σ)
      (((deriv χ t : ℝ) : ℂ) * duhamelPrimitive χ σ t +
        (χ t : ℂ) ^ 2 * (Real.fourierChar (σ * t) : ℂ)) t := by
  have he : duhamelMode χ σ = (fun u : ℝ => (χ u : ℂ)) * duhamelPrimitive χ σ := by
    funext u
    rfl
  rw [he]
  convert ((hχ t).hasDerivAt.ofReal_comp).mul
    (hasDerivAt_duhamelPrimitive hχ.continuous σ t) using 1
  ring

/-- The frequency-subtracted derivative has a uniform primitive expression. -/
@[expose] noncomputable def duhamelRemainder (χ : ℝ → ℝ) (σ t : ℝ) : ℂ :=
  ((deriv χ t : ℝ) : ℂ) * duhamelPrimitive χ σ t + (χ t : ℂ) * (χ 0 : ℂ) +
    (χ t : ℂ) * duhamelPrimitive (deriv χ) σ t

/-- The remainder equals `(∂t - 2π i σ)` of the output mode. -/
theorem duhamelRemainder_eq {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (σ t : ℝ) :
    duhamelRemainder χ σ t = deriv (duhamelMode χ σ) t -
      (2 * Real.pi * Complex.I * (σ : ℂ)) * duhamelMode χ σ t := by
  rw [(hasDerivAt_duhamelMode (hχ.differentiable (by simp)) σ t).deriv]
  have h := duhamelPrimitive_frequency_identity hχ σ t
  dsimp only [duhamelRemainder, duhamelMode]
  linear_combination (χ t : ℂ) * h

/-- Differentiating the remainder introduces no input-frequency factor. -/
theorem hasDerivAt_duhamelRemainder {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (σ t : ℝ) :
    HasDerivAt (duhamelRemainder χ σ)
      (((deriv (deriv χ) t : ℝ) : ℂ) * duhamelPrimitive χ σ t +
        2 * (χ t : ℂ) * ((deriv χ t : ℝ) : ℂ) * (Real.fourierChar (σ * t) : ℂ) +
        ((deriv χ t : ℝ) : ℂ) * (χ 0 : ℂ) +
        ((deriv χ t : ℝ) : ℂ) * duhamelPrimitive (deriv χ) σ t) t := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have h0 := ((hχ.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have h1 := ((hχ'.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have hP := hasDerivAt_duhamelPrimitive hχ.continuous σ t
  have hQ := hasDerivAt_duhamelPrimitive hχ'.continuous σ t
  have he : duhamelRemainder χ σ =
      ((fun u : ℝ => ((deriv χ u : ℝ) : ℂ)) * duhamelPrimitive χ σ +
        fun u : ℝ => (χ u : ℂ) * (χ 0 : ℂ)) +
          (fun u : ℝ => (χ u : ℂ)) * duhamelPrimitive (deriv χ) σ := by
    funext u
    rfl
  rw [he]
  convert ((h1.mul hP).add (h0.mul_const (χ 0 : ℂ))).add (h0.mul hQ) using 1
  ring

/-- The remainder is smooth for each input frequency. -/
theorem duhamelRemainder_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (σ : ℝ) :
    ContDiff ℝ ∞ (duhamelRemainder χ σ) := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  exact (((Complex.ofRealCLM.contDiff.comp hχ').mul (duhamelPrimitive_contDiff hχ σ)).add
    ((Complex.ofRealCLM.contDiff.comp hχ).mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (χ 0 : ℂ))))).add
      ((Complex.ofRealCLM.contDiff.comp hχ).mul (duhamelPrimitive_contDiff hχ' σ))

/-- The remainder has compact support inherited from the cutoff and its derivative. -/
theorem duhamelRemainder_hasCompactSupport {χ : ℝ → ℝ} (hc : HasCompactSupport χ) (σ : ℝ) :
    HasCompactSupport (duhamelRemainder χ σ) := by
  have h0 : HasCompactSupport (fun t => (χ t : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h1 : HasCompactSupport (fun t => ((deriv χ t : ℝ) : ℂ)) :=
    hc.deriv.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hA := h1.mul_right (f' := duhamelPrimitive χ σ)
  have hB := h0.mul_right (f' := fun _ : ℝ => (χ 0 : ℂ))
  have hC := h0.mul_right (f' := duhamelPrimitive (deriv χ) σ)
  exact (hA.add hB).add hC

end WaveTurbulence.Fourier
