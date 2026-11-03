/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedRectangle
public import WaveTurbulence.Foundations.Fourier.FourTimeMoments
import Mathlib.Tactic

/-!
# The four Lp endpoint moments of a weighted rectangle

No derivatives of the amplitude enter these bounds. The common factor
is an explicit finite expression in the cutoff data and the exponent.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The sum of the four actual endpoint derivative `Lᵖ` norms. -/
@[expose] noncomputable def fourTimeLpNorm (p : ℝ≥0∞) (f : (Fin 2 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ j : Fin 4, eLpNorm (fourTimeDerivatives f j) p

/-- Pointwise-function version of the extended triangle inequality. -/
theorem eLpNorm_fun_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f g : α → ℂ) :
    eLpNorm (fun t => f t + g t) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  convert eLpNorm_add_le (f := f) (g := g) hp using 1

/-- An endpoint product applied directly to the amplitude costs only the two cutoff bounds. -/
theorem eLpNorm_endpoint_amplitude_le {a b : ℝ → ℝ} {R C : ℝ} (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) (p : ℝ≥0∞) :
    eLpNorm (fun t => (a (t 0) : ℂ) * (b (t 1) : ℂ) * A t) p ≤
      ENNReal.ofReal (C ^ 2) * eLpNorm A p := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (endpoint_product_contDiff ha hb hA).continuous.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_endpoint_product_le hC haR hbR t) (norm_nonneg _)

/-- The finite common rectangle moment factor. -/
@[expose] noncomputable def rectangleFourLpFactor (p R C : ℝ) : ℝ≥0∞ :=
  4 * rectangleBaseLpFactor p R C + 4 * rectangleFaceLpFactor p R C + ENNReal.ofReal (C ^ 2)

/-- All four actual derivative norms of a weighted rectangle are controlled by its amplitude. -/
theorem fourTimeLpNorm_weightedRectangle_le {a b : ℝ → ℝ} {R C p : ℝ}
    (hp : 1 < p) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hdaR : EndpointCutoffBounds (deriv a) R C)
    (hbR : EndpointCutoffBounds b R C) (hdbR : EndpointCutoffBounds (deriv b) R C)
    {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    fourTimeLpNorm (ENNReal.ofReal p) (weightedRectangle a b A) ≤
      rectangleFourLpFactor p R C * eLpNorm A (ENNReal.ofReal p) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hda : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  have hdb : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  let B := rectangleBaseLpFactor p R C * eLpNorm A (ENNReal.ofReal p)
  let H := rectangleFaceLpFactor p R C * eLpNorm A (ENNReal.ofReal p)
  let Q := ENNReal.ofReal (C ^ 2) * eLpNorm A (ENNReal.ofReal p)
  have h₀ : eLpNorm (weightedRectangle a b A) (ENNReal.ofReal p) ≤ B :=
    eLpNorm_endpoint_rectangle_le hp hR hC ha hb haR hbR hA
  have h₁ : eLpNorm (WaveTurbulence.partialDeriv 0 (weightedRectangle a b A))
      (ENNReal.ofReal p) ≤ B + H := by
    have he := funext (partialDeriv_weightedRectangle_zero ha hA (b := b))
    rw [he]
    apply (eLpNorm_fun_add_le hp1 _ _).trans
    exact add_le_add (eLpNorm_endpoint_rectangle_le hp hR hC hda hb hdaR hbR hA)
      (eLpNorm_endpoint_rectangle_row_le hp hR hC ha hb haR hbR hA)
  have h₂ : eLpNorm (WaveTurbulence.partialDeriv 1 (weightedRectangle a b A))
      (ENNReal.ofReal p) ≤ B + H := by
    have he := funext (partialDeriv_weightedRectangle_one hb hA (a := a))
    rw [he]
    apply (eLpNorm_fun_add_le hp1 _ _).trans
    exact add_le_add (eLpNorm_endpoint_rectangle_le hp hR hC ha hdb haR hdbR hA)
      (eLpNorm_endpoint_rectangle_column_le hp hR hC ha hb haR hbR hA)
  have h₃ : eLpNorm (WaveTurbulence.partialDeriv 0
      (WaveTurbulence.partialDeriv 1 (weightedRectangle a b A))) (ENNReal.ofReal p) ≤
      B + H + H + Q := by
    have he := funext (partialDeriv_weightedRectangle_mixed ha hb hA)
    rw [he]
    apply (eLpNorm_fun_add_le hp1 _ _).trans
    apply add_le_add _ (eLpNorm_endpoint_amplitude_le hC ha hb haR hbR hA _)
    apply (eLpNorm_fun_add_le hp1 _ _).trans
    apply add_le_add _ (eLpNorm_endpoint_rectangle_column_le hp hR hC hda hb hdaR hbR hA)
    apply (eLpNorm_fun_add_le hp1 _ _).trans
    exact add_le_add (eLpNorm_endpoint_rectangle_le hp hR hC hda hdb hdaR hdbR hA)
      (eLpNorm_endpoint_rectangle_row_le hp hR hC ha hdb haR hdbR hA)
  simp only [fourTimeLpNorm, fourTimeDerivatives, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  apply (add_le_add h₀ (add_le_add h₁ (add_le_add h₂ h₃))).trans_eq
  dsimp [B, H, Q, rectangleFourLpFactor]
  ring

/-- Finiteness of the complete rectangle moment factor. -/
theorem rectangleFourLpFactor_ne_top {p : ℝ} (hp : 1 < p) (R C : ℝ) :
    rectangleFourLpFactor p R C ≠ ⊤ := by
  obtain ⟨hb, hf⟩ := rectangleLpFactors_ne_top hp R C
  unfold rectangleFourLpFactor
  finiteness

end WaveTurbulence.Fourier
