/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintSigned.KernelIntegrability
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-!
# Fourier transformation under a genuinely integrable parameter integral

This is the Fubini step for the explicit local extension. The hypothesis
is product-space integrability, established separately for the literal
source phase and exponential rectangle.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintSigned

/-- Product integrability permits commuting the time Fourier transform and
an auxiliary parameter integral. -/
theorem timeFourier_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {r : ℕ} (F : α → (Fin r → ℝ) → ℂ)
    (hF : Integrable (fun p : α × (Fin r → ℝ) => F p.1 p.2) (μ.prod volume))
    (ξ : Fin r → ℝ) :
    Fourier.timeFourier (fun z => ∫ a, F a z ∂μ) ξ =
      ∫ a, Fourier.timeFourier (F a) ξ ∂μ := by
  have hc : Continuous (fun z : Fin r → ℝ =>
      Real.fourierChar (-Fourier.timePairing r z ξ)) := by
    apply Real.continuous_fourierChar.comp
    change Continuous (fun z : Fin r → ℝ => -(∑ j, z j * ξ j))
    fun_prop
  have hi : Integrable (fun p : α × (Fin r → ℝ) =>
      Real.fourierChar (-Fourier.timePairing r p.2 ξ) • F p.1 p.2) (μ.prod volume) := by
    apply hF.norm.mono'
    · exact (hc.aestronglyMeasurable.comp_snd).smul hF.aestronglyMeasurable
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  unfold Fourier.timeFourier VectorFourier.fourierIntegral
  simp_rw [Circle.smul_def, ← integral_smul]
  have hs := hi.swap
  change Integrable (Function.uncurry (fun z a =>
    (Real.fourierChar (-Fourier.timePairing r z ξ) : ℂ) • F a z)) (volume.prod μ) at hs
  exact integral_integral_swap hs

end WaveTurbulence.SumintSigned
