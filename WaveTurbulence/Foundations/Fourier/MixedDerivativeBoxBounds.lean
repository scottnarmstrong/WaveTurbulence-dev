/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedDerivativeStripBounds
public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
import Mathlib.Tactic

/-!
# Local amplitude and first-derivative bounds on a fixed time box

Only the cutoff box contributes volume factors. The support of the
smooth compact input may be arbitrarily large.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Local amplitude `L¹` control with the exact box-volume factor. -/
theorem boxIntegral_amplitude_le_mixed {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (R : ℝ) :
    boxIntegral 2 (fun v => ‖F v‖ₑ) R ≤
      volume (Icc (-R) R) ^ 2 * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  calc
    _ ≤ boxIntegral 2 (fun _ => ∫⁻ x, ‖mixedTimePartial F x‖ₑ) R :=
      boxIntegral_mono 2 (enorm_le_lintegral_mixedTimePartial hF hc) R
    _ = _ := boxIntegral_const 2 _ R

/-- Local `∂₀F` control with one transverse box-width factor. -/
theorem boxIntegral_partial_zero_le_mixed {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (R : ℝ) :
    boxIntegral 2 (fun v => ‖WaveTurbulence.partialDeriv 0 F v‖ₑ) R ≤
      volume (Icc (-R) R) * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  rw [boxIntegral_two]
  exact (setLIntegral_le_lintegral _ _).trans
    (lintegral_partial_zero_strip_le hF hc (Icc (-R) R) isCompact_Icc.measure_lt_top.ne)

/-- Local `∂₁F` control has the same width factor. -/
theorem boxIntegral_partial_one_le_mixed {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (R : ℝ) :
    boxIntegral 2 (fun v => ‖WaveTurbulence.partialDeriv 1 F v‖ₑ) R ≤
      volume (Icc (-R) R) * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  have hp := WaveTurbulence.contDiff_infty_partialDeriv hF 1
  have hm : Measurable (fun z : ℝ × ℝ => ‖WaveTurbulence.partialDeriv 1 F ![z.1, z.2]‖ₑ) :=
    (hp.continuous.comp (by fun_prop)).measurable.enorm
  rw [boxIntegral_two, lintegral_lintegral_swap
    (f := fun u v : ℝ => ‖WaveTurbulence.partialDeriv 1 F ![u, v]‖ₑ)
    (μ := volume.restrict (Icc (-R) R)) (ν := volume.restrict (Icc (-R) R)) hm.aemeasurable]
  exact (setLIntegral_le_lintegral _ _).trans
    (lintegral_partial_one_strip_le hF hc (Icc (-R) R) isCompact_Icc.measure_lt_top.ne)

end WaveTurbulence.Fourier
