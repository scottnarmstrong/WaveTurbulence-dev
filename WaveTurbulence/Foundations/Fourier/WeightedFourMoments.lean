/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedFirstMoments
public import WaveTurbulence.Foundations.Fourier.WeightedMixedDerivative
public import WaveTurbulence.Foundations.Fourier.OrderedFaceRegularity
import Mathlib.Tactic

/-!
# All four endpoint moments of a weighted ordered operator

A single polynomial in the cutoff bound and box width controls the
actual sum of four endpoint derivative `L¹` norms. The amplitude is never
differentiated in this estimate.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Explicit finite factor in the four endpoint moment estimate. -/
@[expose] noncomputable def orderedFourMomentFactor (R C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C ^ 2) * (4 * volume (Icc (-R) R) ^ 2 + 4 * volume (Icc (-R) R) + 1)

/-- Uniform mixed endpoint derivative `L¹` bound, exposing both boundary faces. -/
theorem lintegral_partial_mixed_weighted_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    {A : (Fin (n + 2) → ℝ) → ℂ} (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (haR : EndpointCutoffBounds a R C) (hdaR : EndpointCutoffBounds (deriv a) R C)
    (hbR : EndpointCutoffBounds b R C) (hdbR : EndpointCutoffBounds (deriv b) R C) :
    (∫⁻ t, ‖WaveTurbulence.partialDeriv 0
      (WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 2) a b A)) t‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * (volume (Icc (-R) R) ^ 2 + volume (Icc (-R) R) +
        volume (Icc (-R) R) + 1) * boxIntegral (n + 2) (fun v => ‖A v‖ₑ) R := by
  let T₀ := weightedOrderedIntegral (n + 2) (deriv a) (deriv b) A
  let T₁ := fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) *
    orderedIntegral (n + 1) (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1)
  let T₂ := fun t : Fin 2 → ℝ => ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) *
    orderedIntegral (n + 1) (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1)
  let T₃ := fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * (b (t 1) : ℂ) *
    orderedIntegral n (fun v => A (Fin.snoc (Fin.cons (t 0) v) (t 1))) (t 0) (t 1)
  have hda : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  have hdb : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  have hT₀ : ContDiff ℝ ∞ T₀ := weightedOrderedIntegral_contDiff hda hdb hA
  have hT₁ : ContDiff ℝ ∞ T₁ := endpoint_product_contDiff ha hdb (ordered_upper_face_contDiff hA)
  have hT₂ : ContDiff ℝ ∞ T₂ := endpoint_product_contDiff hda hb (ordered_lower_face_contDiff hA)
  have he : WaveTurbulence.partialDeriv 0
      (WaveTurbulence.partialDeriv 1 (weightedOrderedIntegral (n + 2) a b A)) =
      fun t => T₀ t + T₁ t - T₂ t - T₃ t := by
    funext t
    exact partialDeriv_weightedOrderedIntegral_mixed ha hb hA t
  have hB₀ := lintegral_enorm_weightedOrderedIntegral_le hC hdaR hdbR A
  have hB₁ := lintegral_enorm_ordered_upper_face_le hC haR hdbR hA.continuous.measurable
  have hB₂ := lintegral_enorm_ordered_lower_face_le hC hdaR hbR hA.continuous.measurable
  have hB₃ : (∫⁻ t, ‖T₃ t‖ₑ) ≤ ENNReal.ofReal (C ^ 2) *
      boxIntegral (n + 2) (fun v => ‖A v‖ₑ) R := by
    simpa only [T₃, Fin.cons_snoc_eq_snoc_cons] using
      lintegral_enorm_ordered_mixed_face_le hC haR hbR hA.continuous.measurable
  rw [he]
  apply (lintegral_enorm_add_sub_sub_le hT₀.continuous.measurable
    hT₁.continuous.measurable hT₂.continuous.measurable).trans
  exact (add_le_add (add_le_add (add_le_add hB₀ hB₁) hB₂) hB₃).trans_eq (by ring)

/-- All four endpoint moments are controlled by the same amplitude box integral. -/
theorem fourTimeMomentNorm_weighted_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    {A : (Fin (n + 2) → ℝ) → ℂ} (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (haR : EndpointCutoffBounds a R C) (hdaR : EndpointCutoffBounds (deriv a) R C)
    (hbR : EndpointCutoffBounds b R C) (hdbR : EndpointCutoffBounds (deriv b) R C) :
    fourTimeMomentNorm (weightedOrderedIntegral (n + 2) a b A) ≤
      orderedFourMomentFactor R C * boxIntegral (n + 2) (fun v => ‖A v‖ₑ) R := by
  have h₀ := lintegral_enorm_weightedOrderedIntegral_le hC haR hbR A
  have h₁ := lintegral_partial_upper_weighted_le hC ha hb hA haR hdaR hbR
  have h₂ := lintegral_partial_lower_weighted_le hC ha hb hA haR hbR hdbR
  have h₃ := lintegral_partial_mixed_weighted_le hC ha hb hA haR hdaR hbR hdbR
  simp only [fourTimeMomentNorm, fourTimeDerivatives, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  exact (add_le_add h₀ (add_le_add h₁ (add_le_add h₂ h₃))).trans_eq (by
    unfold orderedFourMomentFactor
    ring)

/-- The endpoint moment factor is finite for every real cutoff radius and bound. -/
theorem orderedFourMomentFactor_ne_top (R C : ℝ) : orderedFourMomentFactor R C ≠ ⊤ := by
  have hw : volume (Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  unfold orderedFourMomentFactor
  finiteness

end WaveTurbulence.Fourier
