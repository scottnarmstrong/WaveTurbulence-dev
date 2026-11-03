/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedDerivativeControl
public import WaveTurbulence.Foundations.Fourier.PartialDerivativeSymmetry
public import WaveTurbulence.Foundations.Fourier.TwoCoordinateIntegration
import Mathlib.Tactic

/-!
# Local first-derivative bounds from the mixed derivative

Compact support supplies the one-dimensional fundamental theorem in the
other coordinate. Integrating over a finite-width strip costs only that
width, independently of the support of the input function.
-/

public section

open MeasureTheory Function
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- A first derivative is controlled by a marginal of the mixed derivative. -/
theorem enorm_partial_one_le_mixed_marginal {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (u v : ℝ) :
    ‖WaveTurbulence.partialDeriv 1 F ![u, v]‖ₑ ≤
      ∫⁻ a : ℝ, ‖mixedTimePartial F ![a, v]‖ₑ := by
  have hd := WaveTurbulence.contDiff_infty_partialDeriv hF 1
  have hs := hasCompactSupport_partialDeriv (hF.differentiable (by simp)) hc 1
  apply (enorm_le_lintegral_partialDeriv hd hs 0 ![u, v]).trans_eq
  apply lintegral_congr
  intro a
  have he : update ![u, v] 0 a = ![a, v] := by ext j; fin_cases j <;> simp
  rw [he]
  rfl

/-- The other first derivative uses the same prescribed mixed derivative, by symmetry. -/
theorem enorm_partial_zero_le_mixed_marginal {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (u v : ℝ) :
    ‖WaveTurbulence.partialDeriv 0 F ![u, v]‖ₑ ≤
      ∫⁻ b : ℝ, ‖mixedTimePartial F ![u, b]‖ₑ := by
  have hd := WaveTurbulence.contDiff_infty_partialDeriv hF 0
  have hs := hasCompactSupport_partialDeriv (hF.differentiable (by simp)) hc 0
  apply (enorm_le_lintegral_partialDeriv hd hs 1 ![u, v]).trans_eq
  apply lintegral_congr
  intro b
  have he : update ![u, v] 1 b = ![u, b] := by ext j; fin_cases j <;> simp
  rw [he, partialDeriv_comm hF 1 0]
  rfl

/-- Integration of `∂₁F` over a finite-width strip costs only the width of that strip. -/
theorem lintegral_partial_one_strip_le {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (S : Set ℝ) (hS : volume S ≠ ⊤) :
    (∫⁻ v : ℝ, ∫⁻ u in S, ‖WaveTurbulence.partialDeriv 1 F ![u, v]‖ₑ) ≤
      volume S * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  have hm : Measurable (fun x => ‖mixedTimePartial F x‖ₑ) :=
    (WaveTurbulence.contDiff_infty_partialDeriv
      (WaveTurbulence.contDiff_infty_partialDeriv hF 1) 0).continuous.measurable.enorm
  calc
    _ ≤ ∫⁻ v : ℝ, ∫⁻ _u in S, ∫⁻ a : ℝ, ‖mixedTimePartial F ![a, v]‖ₑ := by
      apply lintegral_mono
      intro v
      exact lintegral_mono (fun u => enorm_partial_one_le_mixed_marginal hF hc u v)
    _ = ∫⁻ v : ℝ, volume S * ∫⁻ a : ℝ, ‖mixedTimePartial F ![a, v]‖ₑ := by
      apply lintegral_congr
      intro v
      simp [mul_comm]
    _ = volume S * ∫⁻ v : ℝ, ∫⁻ a : ℝ, ‖mixedTimePartial F ![a, v]‖ₑ :=
      lintegral_const_mul' _ _ hS
    _ = _ := congrArg (fun z => volume S * z) (lintegral_two_coordinates_symm hm).symm

/-- Integration of `∂₀F` over the transverse finite-width strip has the same bound. -/
theorem lintegral_partial_zero_strip_le {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (S : Set ℝ) (hS : volume S ≠ ⊤) :
    (∫⁻ u : ℝ, ∫⁻ v in S, ‖WaveTurbulence.partialDeriv 0 F ![u, v]‖ₑ) ≤
      volume S * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  have hm : Measurable (fun x => ‖mixedTimePartial F x‖ₑ) :=
    (WaveTurbulence.contDiff_infty_partialDeriv
      (WaveTurbulence.contDiff_infty_partialDeriv hF 1) 0).continuous.measurable.enorm
  calc
    _ ≤ ∫⁻ u : ℝ, ∫⁻ _v in S, ∫⁻ b : ℝ, ‖mixedTimePartial F ![u, b]‖ₑ := by
      apply lintegral_mono
      intro u
      exact lintegral_mono (fun v => enorm_partial_zero_le_mixed_marginal hF hc u v)
    _ = ∫⁻ u : ℝ, volume S * ∫⁻ b : ℝ, ‖mixedTimePartial F ![u, b]‖ₑ := by
      apply lintegral_congr
      intro u
      simp [mul_comm]
    _ = volume S * ∫⁻ u : ℝ, ∫⁻ b : ℝ, ‖mixedTimePartial F ![u, b]‖ₑ :=
      lintegral_const_mul' _ _ hS
    _ = _ := congrArg (fun z => volume S * z) (lintegral_two_coordinates hm).symm

end WaveTurbulence.Fourier
