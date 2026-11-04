/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TimeTraceSynthesis
public import WaveTurbulence.Foundations.Incoh.IntegrableKernelMixture
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm

/-!
# Integrability of the fixed-clock synthesis kernels

The output cutoff supplies one common time dominator, independently of
the surviving Fourier frequency and of the frozen clock value.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

@[fun_prop] theorem measurable_eraseTimeFrequency {r : ℕ} (j : Fin r) :
    Measurable (eraseTimeFrequency j) := measurable_update_left

/-- The frozen-frequency synthesis kernel is jointly measurable. -/
theorem stronglyMeasurable_frozenModulation {r : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (j : Fin r) : StronglyMeasurable (fun z : (Fin r → ℝ) × (Fin r → ℝ) => frozenModulation χ j z.1 z.2) := by
  have hs : Measurable (fun z : (Fin r → ℝ) × (Fin r → ℝ) =>
      Fourier.timePairing r z.1 (eraseTimeFrequency j z.2)) := by
    change Measurable (fun z : (Fin r → ℝ) × (Fin r → ℝ) => ∑ i, z.1 i * eraseTimeFrequency j z.2 i)
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp (measurable_eraseTimeFrequency j)).comp measurable_snd)
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
  have hp : Measurable (fun z : (Fin r → ℝ) × (Fin r → ℝ) =>
      (Real.fourierChar (Fourier.timePairing r z.1 (eraseTimeFrequency j z.2)) : ℂ)) :=
    hcoe.measurable.comp (Real.continuous_fourierChar.measurable.comp hs)
  exact hp.stronglyMeasurable.mul
    ((Fourier.coordinateCutoff_contDiff hχ).continuous.stronglyMeasurable.comp_measurable measurable_fst)

/-- The cutoff norm is an integrable common dominator. -/
theorem integrable_norm_coordinateCutoff {r : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun t : Fin r → ℝ => ‖Fourier.coordinateCutoff χ t‖) :=
  ((Fourier.coordinateCutoff_contDiff hχ).continuous.integrable_of_hasCompactSupport
    (Fourier.coordinateCutoff_hasCompactSupport hcχ)).norm

/-- Every synthesis kernel is time integrable. -/
theorem integrable_frozenModulation {r : ℕ} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (j : Fin r) (ξ : Fin r → ℝ) :
    Integrable (fun t => frozenModulation χ j t ξ) :=
  integrable_kernel_slice_of_dominator (stronglyMeasurable_frozenModulation hχ j)
    (integrable_norm_coordinateCutoff hχ hcχ) (fun t ξ => (norm_frozenModulation χ j t ξ).le) ξ

end WaveTurbulence.Incoh
