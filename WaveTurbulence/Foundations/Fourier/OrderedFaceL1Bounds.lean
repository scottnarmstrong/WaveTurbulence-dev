/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.EndpointL1Bound
public import WaveTurbulence.Foundations.Fourier.BoxFaceMarginals
import Mathlib.Tactic

/-!
# Time L¹ bounds for the ordered boundary faces

All four endpoint moments are bounded by the same amplitude box integral.
The unused output endpoints contribute zero, one, or two box-width factors.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- The upper boundary face costs one unused output interval. -/
theorem lintegral_enorm_ordered_upper_face_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    (hC : 0 ≤ C) (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    {A : (Fin (n + 1) → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t : Fin 2 → ℝ, ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) *
      orderedIntegral n (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1)‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R := by
  apply (lintegral_enorm_endpoint_product_le hC ha hb
    (fun t => orderedIntegral n (fun v => A (Fin.cons (t 0) v)) (t 0) (t 1))).trans
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
        boxIntegral n (fun v => ‖A (Fin.cons (t 0) v)‖ₑ) R := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hp := (mem_two_time_box_iff R t).mp ht
      exact enorm_orderedIntegral_le_boxIntegral n _ R (t 0) (t 1) (abs_le.mp hp.1) (abs_le.mp hp.2)
    _ = _ := by rw [box_upper_face_marginal hA.enorm R]; ring

/-- The lower boundary face costs one unused output interval. -/
theorem lintegral_enorm_ordered_lower_face_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    (hC : 0 ≤ C) (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    {A : (Fin (n + 1) → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t : Fin 2 → ℝ, ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) *
      orderedIntegral n (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1)‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) * boxIntegral (n + 1) (fun v => ‖A v‖ₑ) R := by
  apply (lintegral_enorm_endpoint_product_le hC ha hb
    (fun t => orderedIntegral n (fun v => A (Fin.snoc v (t 1))) (t 0) (t 1))).trans
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
        boxIntegral n (fun v => ‖A (Fin.snoc v (t 1))‖ₑ) R := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hp := (mem_two_time_box_iff R t).mp ht
      exact enorm_orderedIntegral_le_boxIntegral n _ R (t 0) (t 1) (abs_le.mp hp.1) (abs_le.mp hp.2)
    _ = _ := by rw [box_lower_face_marginal hA.enorm R]; ring

/-- The mixed boundary face uses both output times as amplitude coordinates. -/
theorem lintegral_enorm_ordered_mixed_face_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    (hC : 0 ≤ C) (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    {A : (Fin (n + 2) → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t : Fin 2 → ℝ, ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) *
      orderedIntegral n (fun v => A (Fin.cons (t 0) (Fin.snoc v (t 1)))) (t 0) (t 1)‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * boxIntegral (n + 2) (fun v => ‖A v‖ₑ) R := by
  apply (lintegral_enorm_endpoint_product_le hC ha hb
    (fun t => orderedIntegral n (fun v => A (Fin.cons (t 0) (Fin.snoc v (t 1)))) (t 0) (t 1))).trans
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
        boxIntegral n (fun v => ‖A (Fin.cons (t 0) (Fin.snoc v (t 1)))‖ₑ) R := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hp := (mem_two_time_box_iff R t).mp ht
      exact enorm_orderedIntegral_le_boxIntegral n _ R (t 0) (t 1) (abs_le.mp hp.1) (abs_le.mp hp.2)
    _ = _ := by rw [box_mixed_face_marginal hA.enorm R]

end WaveTurbulence.Fourier
