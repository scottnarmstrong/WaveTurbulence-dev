/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedFaceL1Bounds
public import WaveTurbulence.Foundations.Fourier.FourMomentLinearity
import Mathlib.Tactic

/-!
# First endpoint moment bounds for weighted ordered integration

The product rule exposes one cutoff derivative and one boundary face.
Both are controlled by the same amplitude integral over the fixed box.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Uniform upper-time derivative `L¹` bound. -/
theorem lintegral_partial_upper_weighted_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    {A : (Fin (n + 1) → ℝ) → ℂ} (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (haR : EndpointCutoffBounds a R C) (hdaR : EndpointCutoffBounds (deriv a) R C)
    (hbR : EndpointCutoffBounds b R C) :
    (∫⁻ t, ‖WaveTurbulence.partialDeriv 0 (weightedOrderedIntegral (n + 1) a b A) t‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * (volume (Icc (-R) R) ^ 2 + volume (Icc (-R) R)) *
        boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R := by
  let T₀ := weightedOrderedIntegral (n + 1) (deriv a) b A
  let T₁ := fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * (b (t 1) : ℂ) *
    orderedIntegral n (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1)
  have hT₀ : ContDiff ℝ ∞ T₀ :=
    weightedOrderedIntegral_contDiff (contDiff_infty_iff_deriv.mp ha).2 hb hA
  have he : WaveTurbulence.partialDeriv 0 (weightedOrderedIntegral (n + 1) a b A) =
      fun t => T₀ t + T₁ t := by
    funext t
    exact partialDeriv_weightedOrderedIntegral_upper ha hA t
  rw [he]
  calc
    _ ≤ (∫⁻ t, ‖T₀ t‖ₑ) + ∫⁻ t, ‖T₁ t‖ₑ := lintegral_enorm_add_le hT₀.continuous.measurable
    _ ≤ (ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) ^ 2 * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R) +
        ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R :=
      add_le_add (lintegral_enorm_weightedOrderedIntegral_le hC hdaR hbR A)
        (lintegral_enorm_ordered_upper_face_le hC haR hbR hA.continuous.measurable)
    _ = _ := by ring

/-- Uniform lower-time derivative `L¹` bound. -/
theorem lintegral_partial_lower_weighted_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    {A : (Fin (n + 1) → ℝ) → ℂ} (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    (hdbR : EndpointCutoffBounds (deriv b) R C) :
    (∫⁻ t, ‖WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 1) a b A) t‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * (volume (Icc (-R) R) ^ 2 + volume (Icc (-R) R)) *
        boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R := by
  let T₀ := weightedOrderedIntegral (n + 1) a (deriv b) A
  let T₁ := fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * (b (t 1) : ℂ) *
    orderedIntegral n (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1)
  have hT₀ : ContDiff ℝ ∞ T₀ :=
    weightedOrderedIntegral_contDiff ha (contDiff_infty_iff_deriv.mp hb).2 hA
  have he : WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 1) a b A) =
      fun t => T₀ t - T₁ t := by
    funext t
    exact partialDeriv_weightedOrderedIntegral_lower hb hA t
  rw [he]
  calc
    _ ≤ (∫⁻ t, ‖T₀ t‖ₑ) + ∫⁻ t, ‖T₁ t‖ₑ := lintegral_enorm_sub_le hT₀.continuous.measurable
    _ ≤ (ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) ^ 2 * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R) +
        ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R :=
      add_le_add (lintegral_enorm_weightedOrderedIntegral_le hC haR hdbR A)
        (lintegral_enorm_ordered_lower_face_le hC haR hbR hA.continuous.measurable)
    _ = _ := by ring

end WaveTurbulence.Fourier
