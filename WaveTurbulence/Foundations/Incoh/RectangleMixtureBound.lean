/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectangleKernelDominator
public import WaveTurbulence.Foundations.Incoh.IntegrableKernelMixture

/-!
# Rectangular phase mixtures with internal-clock-dependent endpoints

The only amplitude cost is its actual absolute integral. All kernel
measurability and Fubini premises are proved from the fixed time cutoff.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Integrating the universal triangular family costs only the amplitude mass. -/
theorem mixedFourierNorm00_rectangleU_mixture_le {χ : ℝ → ℝ} (hχ : Measurable χ)
    (h : Fourier.CutoffControl χ) {U V : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (A : V → U → ℂ) (p : V → U → Mom 6)
    (hiA : ∀ v, Integrable (A v) μ) (hmA : ∀ v, StronglyMeasurable (A v))
    (hp : ∀ v, Measurable (p v)) {M : ℝ≥0∞} (hmass : ∀ v, (∫⁻ u, ‖A v u‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4) (fun t v => ∫ u, A v u * universalRectangleU χ t (p v u) ∂μ) ≤
      M * Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleU χ) := by
  have hK := stronglyMeasurable_universalRectangleU hχ
  have hB := integrable_rectangleKernelDominator h 2
  have hb := fun t p => norm_universalRectangleU_le h p t
  exact mixedFourierNorm00_integral_mixture_le μ (1 / 4) A p (universalRectangleU χ)
    (integrable_kernel_slice_of_dominator hK hB hb) (fun v => (hmA v).aestronglyMeasurable)
    (fun v => integrable_joint_kernel_mixture μ hK hB hb (hiA v) (hmA v) (hp v)) hmass

/-- The fourfold family has the same mixture estimate. -/
theorem mixedFourierNorm00_rectangleV_mixture_le {χ : ℝ → ℝ} (hχ : Measurable χ)
    (h : Fourier.CutoffControl χ) {U V : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (A : V → U → ℂ) (p : V → U → Mom 6)
    (hiA : ∀ v, Integrable (A v) μ) (hmA : ∀ v, StronglyMeasurable (A v))
    (hp : ∀ v, Measurable (p v)) {M : ℝ≥0∞} (hmass : ∀ v, (∫⁻ u, ‖A v u‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4) (fun t v => ∫ u, A v u * universalRectangleV χ t (p v u) ∂μ) ≤
      M * Fourier.mixedFourierNorm00 (1 / 4) (universalRectangleV χ) := by
  have hK := stronglyMeasurable_universalRectangleV hχ
  have hB := integrable_rectangleKernelDominator h 4
  have hb := fun t p => norm_universalRectangleV_le h p t
  exact mixedFourierNorm00_integral_mixture_le μ (1 / 4) A p (universalRectangleV χ)
    (integrable_kernel_slice_of_dominator hK hB hb) (fun v => (hmA v).aestronglyMeasurable)
    (fun v => integrable_joint_kernel_mixture μ hK hB hb (hiA v) (hmA v) (hp v)) hmass

end WaveTurbulence.Incoh
