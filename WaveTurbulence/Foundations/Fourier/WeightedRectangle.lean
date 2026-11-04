/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.RectangleLpBounds
public import WaveTurbulence.Foundations.Fourier.TimeOperatorRegularity
import Mathlib.Tactic

/-!
# The cut off rectangle and its actual derivatives

The amplitude in this representation includes the two input cutoffs;
the two output cutoffs are kept separate in the product rules.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Rectangular integration with separate output endpoint cutoffs. -/
@[expose] noncomputable def weightedRectangle (a b : ℝ → ℝ)
    (A : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  (a (t 0) : ℂ) * (b (t 1) : ℂ) * rectanglePrimitive A t

/-- The rectangular source operator is this literal weighted rectangle. -/
theorem cutoffDoubleIntegral_eq_weightedRectangle (χ : ℝ → ℝ) (F : (Fin 2 → ℝ) → ℂ) :
    cutoffDoubleIntegral χ F = weightedRectangle χ χ (triangleAmplitude χ F) := by
  funext t
  simp [cutoffDoubleIntegral, weightedRectangle, rectanglePrimitive, triangleAmplitude,
    coordinateCutoff, Fin.prod_univ_two, mul_assoc]

/-- Smoothness of a weighted rectangle. -/
theorem weightedRectangle_contDiff {a b : ℝ → ℝ} {A : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (weightedRectangle a b A) :=
  endpoint_product_contDiff ha hb (rectanglePrimitive_contDiff hA)

/-- First endpoint derivative exposes the row primitive. -/
theorem partialDeriv_weightedRectangle_zero {a b : ℝ → ℝ} {A : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (weightedRectangle a b A) t =
      weightedRectangle (deriv a) b A t +
        (a (t 0) : ℂ) * (b (t 1) : ℂ) * ∫ v in (0 : ℝ)..t 1, A ![t 0, v] := by
  change WaveTurbulence.partialDeriv 0 (fun z =>
    (a (z 0) : ℂ) * (b (z 1) : ℂ) * rectanglePrimitive A z) t = _
  rw [partialDeriv_endpoint_product_zero ha (rectanglePrimitive_contDiff hA),
    partialDeriv_rectanglePrimitive_zero hA]
  rfl

/-- Second endpoint derivative exposes the column primitive. -/
theorem partialDeriv_weightedRectangle_one {a b : ℝ → ℝ} {A : (Fin 2 → ℝ) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A) (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 1 (weightedRectangle a b A) t =
      weightedRectangle a (deriv b) A t +
        (a (t 0) : ℂ) * (b (t 1) : ℂ) * ∫ u in (0 : ℝ)..t 0, A ![u, t 1] := by
  change WaveTurbulence.partialDeriv 1 (fun z =>
    (a (z 0) : ℂ) * (b (z 1) : ℂ) * rectanglePrimitive A z) t = _
  rw [partialDeriv_endpoint_product_one hb (rectanglePrimitive_contDiff hA),
    partialDeriv_rectanglePrimitive_one hA]
  rfl

/-- The mixed derivative charges the base, both faces and the amplitude, without differentiating the amplitude. -/
theorem partialDeriv_weightedRectangle_mixed {a b : ℝ → ℝ} {A : (Fin 2 → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (t : Fin 2 → ℝ) :
    WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 (weightedRectangle a b A)) t =
      weightedRectangle (deriv a) (deriv b) A t +
      (a (t 0) : ℂ) * ((deriv b (t 1) : ℝ) : ℂ) * (∫ v in (0 : ℝ)..t 1, A ![t 0, v]) +
      ((deriv a (t 0) : ℝ) : ℂ) * (b (t 1) : ℂ) * (∫ u in (0 : ℝ)..t 0, A ![u, t 1]) +
      (a (t 0) : ℂ) * (b (t 1) : ℂ) * A t := by
  change WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 (fun z =>
    (a (z 0) : ℂ) * (b (z 1) : ℂ) * rectanglePrimitive A z)) t = _
  rw [partialDeriv_endpoint_product_mixed ha hb (rectanglePrimitive_contDiff hA),
    partialDeriv_rectanglePrimitive_zero hA, partialDeriv_rectanglePrimitive_one hA,
    partialDeriv_rectanglePrimitive_mixed hA]
  rfl

/-- Output endpoint bounds imply compact support of the weighted rectangle. -/
theorem weightedRectangle_hasCompactSupport {a b : ℝ → ℝ} {R C : ℝ}
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (A : (Fin 2 → ℝ) → ℂ) : HasCompactSupport (weightedRectangle a b A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := fun _ : Fin 2 => -R) (b := fun _ => R))
  intro t ht
  rw [weightedRectangle, endpoint_product_eq_zero_outside ha hb t ht, zero_mul]

end WaveTurbulence.Fourier
