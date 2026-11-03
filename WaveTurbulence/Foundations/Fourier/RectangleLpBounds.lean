/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.RectanglePowerBounds
public import WaveTurbulence.Foundations.Fourier.LpFromPowerBound
public import WaveTurbulence.Foundations.Fourier.EndpointProductDerivatives
import Mathlib.Tactic

/-!
# Local Lp bounds for the rectangle and its boundary faces

Every displayed factor is finite when `p > 1`. The estimates use only
the amplitude norm and the output cutoff radius and bound.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- A generic localized power estimate, followed by the `Lᵖ` root. -/
theorem eLpNorm_endpoint_product_le_of_power {a b : ℝ → ℝ} {R C p : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    {G A : (Fin 2 → ℝ) → ℂ} (hG : ContDiff ℝ ∞ G) (hA : Measurable A)
    {K : ℝ≥0∞}
    (hpower : (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), ‖G t‖ₑ ^ p) ≤
      K * boxIntegral 2 (fun v => ‖A v‖ₑ ^ p) R) :
    eLpNorm (fun t => (a (t 0) : ℂ) * (b (t 1) : ℂ) * G t) (ENNReal.ofReal p) ≤
      ((ENNReal.ofReal (C ^ 2)) ^ p * K) ^ (1 / p) * eLpNorm A (ENNReal.ofReal p) := by
  apply eLpNorm_le_of_power_bound hp
    (endpoint_product_contDiff ha hb hG).continuous.aestronglyMeasurable
    hA.aestronglyMeasurable
  apply (lintegral_enorm_endpoint_product_rpow_le hC hp haR hbR G).trans
  apply (mul_le_mul_right hpower _).trans
  exact (mul_le_mul_right
    (mul_le_mul_right (boxIntegral_two_le_lintegral (hA.enorm.pow_const p) R) K) _).trans_eq (by ring)

/-- A finite factor for the cut off base rectangle. -/
@[expose] noncomputable def rectangleBaseLpFactor (p R C : ℝ) : ℝ≥0∞ :=
  ((ENNReal.ofReal (C ^ 2)) ^ p *
    ((volume (Icc (-R) R) ^ 2) * (volume (Icc (-R) R) ^ 2) ^ (p - 1))) ^ (1 / p)

/-- A finite factor for either cut off boundary face. -/
@[expose] noncomputable def rectangleFaceLpFactor (p R C : ℝ) : ℝ≥0∞ :=
  ((ENNReal.ofReal (C ^ 2)) ^ p *
    (volume (Icc (-R) R) ^ (p - 1) * volume (Icc (-R) R))) ^ (1 / p)

/-- The cut off base rectangle preserves `Lᵖ` with a cutoff-dependent bound. -/
theorem eLpNorm_endpoint_rectangle_le {a b : ℝ → ℝ} {R C p : ℝ}
    (hp : 1 < p) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    eLpNorm (fun t => (a (t 0) : ℂ) * (b (t 1) : ℂ) * rectanglePrimitive A t)
      (ENNReal.ofReal p) ≤ rectangleBaseLpFactor p R C * eLpNorm A (ENNReal.ofReal p) :=
  eLpNorm_endpoint_product_le_of_power (by linarith) hC ha hb haR hbR
    (rectanglePrimitive_contDiff hA) hA.continuous.measurable
    (lintegral_rectanglePrimitive_rpow_box_le hp hR hA.continuous.measurable)

/-- The row boundary face preserves `Lᵖ`. -/
theorem eLpNorm_endpoint_rectangle_row_le {a b : ℝ → ℝ} {R C p : ℝ}
    (hp : 1 < p) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    eLpNorm (fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * (b (t 1) : ℂ) *
      ∫ v in (0 : ℝ)..t 1, A ![t 0, v]) (ENNReal.ofReal p) ≤
        rectangleFaceLpFactor p R C * eLpNorm A (ENNReal.ofReal p) :=
  eLpNorm_endpoint_product_le_of_power (by linarith) hC ha hb haR hbR
    (rectangle_row_contDiff hA) hA.continuous.measurable
    (lintegral_rectangle_row_rpow_box_le hp hR hA.continuous.measurable)

/-- The column boundary face preserves `Lᵖ`. -/
theorem eLpNorm_endpoint_rectangle_column_le {a b : ℝ → ℝ} {R C p : ℝ}
    (hp : 1 < p) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (haR : EndpointCutoffBounds a R C) (hbR : EndpointCutoffBounds b R C)
    {A : (Fin 2 → ℝ) → ℂ} (hA : ContDiff ℝ ∞ A) :
    eLpNorm (fun t : Fin 2 → ℝ => (a (t 0) : ℂ) * (b (t 1) : ℂ) *
      ∫ u in (0 : ℝ)..t 0, A ![u, t 1]) (ENNReal.ofReal p) ≤
        rectangleFaceLpFactor p R C * eLpNorm A (ENNReal.ofReal p) :=
  eLpNorm_endpoint_product_le_of_power (by linarith) hC ha hb haR hbR
    (rectangle_column_contDiff hA) hA.continuous.measurable
    (lintegral_rectangle_column_rpow_box_le hp hR hA.continuous.measurable)

/-- The two scalar factors have finite values throughout the required range. -/
theorem rectangleLpFactors_ne_top {p : ℝ} (hp : 1 < p) (R C : ℝ) :
    rectangleBaseLpFactor p R C ≠ ⊤ ∧ rectangleFaceLpFactor p R C ≠ ⊤ := by
  have hw : volume (Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  unfold rectangleBaseLpFactor rectangleFaceLpFactor
  constructor <;> finiteness

end WaveTurbulence.Fourier
