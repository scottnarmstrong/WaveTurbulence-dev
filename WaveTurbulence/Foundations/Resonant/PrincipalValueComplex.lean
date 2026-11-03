/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueOneDim
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex test functions in the one-dimensional principal value

DH21 Lemma 6.3 uses complex amplitudes and Fourier phases. We extend the real
cancellation limit to complex test functions by taking real and imaginary parts.
-/

public section

open MeasureTheory Filter Topology

namespace WaveTurbulence

/-- Complex-valued finite truncation of `1/u`. -/
@[expose] noncomputable def pvTruncationComplex (χ : ℝ → ℝ) (μ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ u, (((1 - χ (μ * u)) / u : ℝ) : ℂ) * f u

theorem pvTruncationComplex_eq_parts {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} (hc : Continuous f) (hf : HasCompactSupport f) (μ : ℝ) :
    pvTruncationComplex χ μ f = (pvTruncation χ μ (fun u => (f u).re) : ℂ) +
      (pvTruncation χ μ (fun u => (f u).im) : ℂ) * Complex.I := by
  have hiC : Integrable (fun u : ℝ => (((1 - χ (μ * u)) / u : ℝ) : ℂ) * f u) :=
    ((Complex.continuous_ofReal.comp (hχ.continuous_div μ)).mul hc).integrable_of_hasCompactSupport
      hf.mul_left
  apply Complex.ext
  · simpa [pvTruncationComplex, pvTruncation] using (integral_re hiC).symm
  · simpa [pvTruncationComplex, pvTruncation] using (integral_im hiC).symm

/-- Convergence for complex test functions, including fixed Fourier phases. This
asserts existence only; frequency-uniform estimates require further oscillation bounds. -/
theorem tendsto_pvTruncationComplex {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} (hc : Continuous f) (hd : DifferentiableAt ℝ f 0)
    (hf : HasCompactSupport f) :
    Tendsto (fun μ => pvTruncationComplex χ μ f) atTop
      (𝓝 (((∫ u, pvQuotient (fun v => (f v).re) u) : ℝ) +
        ((∫ u, pvQuotient (fun v => (f v).im) u) : ℝ) * Complex.I)) := by
  have hr := hχ.tendsto_pvTruncation (Complex.continuous_re.comp hc)
    (Complex.reCLM.differentiableAt.comp 0 hd) (hf.comp_left (g := Complex.re) rfl)
  have hi := hχ.tendsto_pvTruncation (Complex.continuous_im.comp hc)
    (Complex.imCLM.differentiableAt.comp 0 hd) (hf.comp_left (g := Complex.im) rfl)
  have hr' := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hi' := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  exact (hr'.add (hi'.mul_const Complex.I)).congr fun μ =>
    (pvTruncationComplex_eq_parts hχ hc hf μ).symm

end WaveTurbulence
