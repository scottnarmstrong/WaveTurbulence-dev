/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CausalKernelMeasurable
public import WaveTurbulence.Foundations.Incoh.CausalBoxRegularity
public import WaveTurbulence.Foundations.Incoh.IntegrableKernelMixture

/-!
# Actual mixtures of the universal causal box kernels

All selected clock bounds and causal orderings remain inside the kernel.
Its common time dominator verifies the joint Fubini premise from the actual
amplitude integrability rather than assuming it.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Integrating the literal causal family costs only the actual amplitude mass. -/
theorem mixedFourierNorm00_causalBox_mixture_le (m : ℕ) {χ : ℝ → ℝ} (hχ : Measurable χ)
    (h : Fourier.CutoffControl χ) {U V : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (A : V → U → ℂ) (p : V → U → CausalBoxData m)
    (hiA : ∀ v, Integrable (A v) μ) (hmA : ∀ v, StronglyMeasurable (A v))
    (hp : ∀ v, Measurable (p v)) {M : ℝ≥0∞} (hmass : ∀ v, (∫⁻ u, ‖A v u‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4)
      (fun t v => ∫ u, A v u * universalCausalBoxKernel m χ t (p v u) ∂μ) ≤
        M * Fourier.mixedFourierNorm00 (1 / 4) (universalCausalBoxKernel m χ) := by
  have hK := stronglyMeasurable_universalCausalBoxKernel m hχ
  have hB := integrable_rectangleKernelDominator h (m + 2)
  have hb (t : Fin 2 → ℝ) (p : CausalBoxData m) :
      ‖universalCausalBoxKernel m χ t p‖ ≤ rectangleKernelDominator h (m + 2) t :=
    norm_causalBoxKernel_le m h p.phase p.lower p.upper p.lower_le_upper t
  exact mixedFourierNorm00_integral_mixture_le μ (1 / 4) A p (universalCausalBoxKernel m χ)
    (integrable_kernel_slice_of_dominator hK hB hb) (fun v => (hmA v).aestronglyMeasurable)
    (fun v => integrable_joint_kernel_mixture μ hK hB hb (hiA v) (hmA v) (hp v)) hmass

end WaveTurbulence.Incoh
