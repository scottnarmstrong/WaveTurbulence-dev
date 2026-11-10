/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothStepMass
public import Mathlib.Analysis.Complex.RealDeriv
public import WaveTurbulence.Foundations.Incoh.SmoothIntervalLimit
public import WaveTurbulence.Foundations.Incoh.PhaseMeasurable
public import WaveTurbulence.Foundations.Fourier.CutoffEightMoments
public import WaveTurbulence.Foundations.Fourier.BoxIntegralLinearity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import WaveTurbulence.Foundations.Fourier.ThreeMomentNorm
public import WaveTurbulence.Foundations.Incoh.MixedFourierFatou
public import Mathlib.Analysis.SpecificLimits.Basic
public import WaveTurbulence.Foundations.Incoh.WeightedOrderedLimit

/-!
# A common time dominator for all rectangular phase kernels

This bound is uniform in phases and interval endpoints. It supplies joint
integrability for actual internal-clock mixtures.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The explicit time dominator for an `m`-fold rectangular phase kernel. -/
@[expose] def rectangleKernelDominator {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ)
    (m : ℕ) : (Fin 2 → ℝ) → ℝ :=
  (Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)).indicator
    (fun _ => h.bound ^ 2 * (h.bound ^ m * (2 * h.radius) ^ m))

theorem integrable_rectangleKernelDominator {χ : ℝ → ℝ} (h : Fourier.CutoffControl χ) (m : ℕ) :
    Integrable (rectangleKernelDominator h m) := by
  unfold rectangleKernelDominator
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const isCompact_Icc.measure_ne_top

end WaveTurbulence.Incoh
