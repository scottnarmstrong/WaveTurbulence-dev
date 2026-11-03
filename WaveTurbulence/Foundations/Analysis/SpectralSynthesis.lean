/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffFourierFormula
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Integrable spectral representations

Functions are synthesized by the inverse Fourier integral. This provides
an actual representation to which the time-integration kernel can be
applied; no spectral estimate is assumed as a source premise.
-/

public section

open MeasureTheory
open scoped FourierTransform Convolution

namespace WaveTurbulence.Analysis

/-- Synthesis of a spectral density by the inverse Fourier transform. -/
@[expose] noncomputable def spectralSynthesis (g : ℝ → ℂ) (t : ℝ) : ℂ := 𝓕⁻ g t

theorem spectralSynthesis_eq_integral (g : ℝ → ℂ) (t : ℝ) :
    spectralSynthesis g t = ∫ s : ℝ, timePhase t s * g s := by
  rw [spectralSynthesis, Real.fourierInv_eq_fourier_neg, fourier_eq_timePhase, neg_neg]

theorem norm_spectralSynthesis_le (g : ℝ → ℂ) (t : ℝ) :
    ‖spectralSynthesis g t‖ ≤ ∫ s : ℝ, ‖g s‖ := by
  rw [spectralSynthesis, Real.fourierInv_eq_fourier_neg]
  exact Real.norm_fourier_le_integral_norm g (-t)

/-- Fourier transforms of integrable densities are continuous. -/
theorem continuous_fourier_of_integrable {g : ℝ → ℂ} (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg

theorem continuous_spectralSynthesis {g : ℝ → ℂ} (hg : Integrable g) :
    Continuous (spectralSynthesis g) := by
  change Continuous (𝓕⁻ g)
  have heq : 𝓕⁻ g = (fun t => 𝓕 g (-t)) := funext (Real.fourierInv_eq_fourier_neg g)
  rw [heq]
  exact (continuous_fourier_of_integrable hg).comp continuous_neg

/-- Multiplication of synthesized functions corresponds to convolution of
their integrable spectral densities. -/
theorem spectralSynthesis_convolution {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) (t : ℝ) :
    spectralSynthesis (g ⋆[ContinuousLinearMap.mul ℂ ℂ] h) t =
      spectralSynthesis g t * spectralSynthesis h t := by
  simp only [spectralSynthesis, Real.fourierInv_eq_fourier_neg,
    Real.fourier_mul_convolution_eq hg hh]

/-- Translation in time changes a spectral density only by a phase. -/
theorem spectralSynthesis_sub (g : ℝ → ℂ) (t a : ℝ) :
    spectralSynthesis g (t - a) =
      spectralSynthesis (fun s => timePhase (-a) s * g s) t := by
  simp only [spectralSynthesis_eq_integral]
  apply integral_congr_ae
  filter_upwards with s
  rw [← mul_assoc, timePhase_add, ← sub_eq_add_neg]

/-- The phase change for a time translation preserves integrability. -/
theorem integrable_timeShiftDensity {g : ℝ → ℂ} (hg : Integrable g) (a : ℝ) :
    Integrable (fun s : ℝ => timePhase (-a) s * g s) := by
  apply hg.norm.mono' ((contDiff_timePhase (-a)).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards with s
  change ‖timePhase (-a) s * g s‖ ≤ ‖g s‖
  rw [norm_mul, norm_timePhase, one_mul]

end WaveTurbulence.Analysis
