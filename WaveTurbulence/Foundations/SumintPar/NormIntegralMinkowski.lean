/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ParametricFourierMeasurability
public import WaveTurbulence.Foundations.SumintPar.NormModulation
public import WaveTurbulence.Foundations.SumintPar.EnvelopeIntegral

/-!
# Integrating localized coefficients in the exact general-output Fourier norm

The output supremum stays inside the frequency integral. Countability of
the output carrier supplies joint measurability; no output cardinality
factor enters the estimate. In the application the output carrier is the
finite common-coset cover.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Joint measurability of the Fourier envelope for a countable output family. -/
theorem measurable_parametric_mixedEnvelope00 {α : Type*} [MeasurableSpace α]
    {r : ℕ} {V : Type*} [Countable V] (F : α → (Fin r → ℝ) → V → ℂ)
    (hFm : ∀ v, Measurable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v)) :
    Measurable (fun p : α × (Fin r → ℝ) => Fourier.mixedFourierEnvelope00 (F p.1) p.2) := by
  unfold Fourier.mixedFourierEnvelope00
  exact Measurable.iSup (fun v =>
    (measurable_parametric_timeFourier (fun a t => F a t v) (hFm v)).enorm)

/-- The Fourier envelope of a parameter integral is bounded before the frequency integral. -/
theorem mixedEnvelope00_integral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {r : ℕ} {V : Type*}
    (F : α → (Fin r → ℝ) → V → ℂ)
    (hFi : ∀ v, Integrable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v) (μ.prod volume))
    (ξ : Fin r → ℝ) :
    Fourier.mixedFourierEnvelope00 (fun t v => ∫ a, F a t v ∂μ) ξ ≤
      ∫⁻ a, Fourier.mixedFourierEnvelope00 (F a) ξ ∂μ := by
  apply iSup_le
  intro v
  change ‖Fourier.timeFourier (fun t => ∫ a, F a t v ∂μ) ξ‖ₑ ≤ _
  rw [timeFourier_integral (fun a t => F a t v) (hFi v) ξ]
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (fun a =>
    le_iSup (fun w => ‖Fourier.timeFourier (fun t => F a t w) ξ‖ₑ) v))

/-- Minkowski for the exact mixed Fourier norm and a countable output carrier. -/
theorem mixedFourierNorm00_integral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {r : ℕ} {V : Type*} [Countable V]
    (s : ℝ) (F : α → (Fin r → ℝ) → V → ℂ)
    (hFm : ∀ v, Measurable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v))
    (hFi : ∀ v, Integrable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v) (μ.prod volume))
    (hFs : ∀ a v, Integrable (fun t => F a t v)) :
    Fourier.mixedFourierNorm00 s (fun t v => ∫ a, F a t v ∂μ) ≤
      ∫⁻ a, Fourier.mixedFourierNorm00 s (F a) ∂μ := by
  have hG (v : V) : Integrable (fun t => ∫ a, F a t v ∂μ) :=
    (hFi v).integral_prod_right
  have hE := measurable_parametric_mixedEnvelope00 F hFm
  rw [Fourier.mixedFourierNorm00_eq_lintegral hG]
  have hh := lintegral_weighted_envelope_le (μ := μ) (ν := (volume : Measure (Fin r → ℝ)))
    (Fourier.timeWeight s) (fun a ξ => Fourier.mixedFourierEnvelope00 (F a) ξ)
    (Fourier.mixedFourierEnvelope00 (fun t v => ∫ a, F a t v ∂μ))
    (Fourier.timeWeight_measurable s) hE (mixedEnvelope00_integral_le F hFi)
  exact hh.trans_eq (lintegral_congr (fun a =>
    (Fourier.mixedFourierNorm00_eq_lintegral (hFs a)).symm))

/-- The same integral inequality for the exact pre-freeze norm. -/
theorem XNorm00_integral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {r : ℕ} {V : Type*} [Countable V]
    (s : ℝ) (F : α → (Fin r → ℝ) → V → ℂ)
    (hFm : ∀ v, Measurable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v))
    (hFi : ∀ v, Integrable (fun p : α × (Fin r → ℝ) => F p.1 p.2 v) (μ.prod volume))
    (hFs : ∀ a v, Integrable (fun t => F a t v)) :
    XNorm00 s (fun t v => ∫ a, F a t v ∂μ) ≤ ∫⁻ a, XNorm00 s (F a) ∂μ := by
  simpa only [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] using
    mixedFourierNorm00_integral_le s F hFm hFi hFs

end WaveTurbulence.SumintPar
