/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedSupport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Endpoint cutoff bounds in time L¹

The two output factors localize time integration to a fixed box.
Their common bound is then extracted before estimating the ordered integral.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- The two-time box has the square of the one-dimensional interval volume. -/
theorem volume_two_time_box (R : ℝ) :
    volume (Icc (fun _ : Fin 2 => -R) (fun _ => R)) = volume (Icc (-R) R) ^ 2 := by
  simp [Real.volume_Icc_pi, Real.volume_Icc, pow_two]

/-- Two endpoint cutoff factors reduce a time `L¹` bound to the fixed output box. -/
theorem lintegral_enorm_endpoint_product_le {a b : ℝ → ℝ} {R C : ℝ} (hC : 0 ≤ C)
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (G : (Fin 2 → ℝ) → ℂ) :
    (∫⁻ t, ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), ‖G t‖ₑ := by
  have hs : support (fun t : Fin 2 → ℝ => ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ) ⊆
      Icc (fun _ : Fin 2 => -R) (fun _ => R) := by
    intro t ht
    by_contra hn
    change ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ ≠ 0 at ht
    rw [endpoint_product_eq_zero_outside ha hb t hn, zero_mul, enorm_zero] at ht
    exact ht rfl
  calc
    _ = ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
        ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ := (setLIntegral_eq_of_support_subset hs).symm
    _ ≤ ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), ENNReal.ofReal (C ^ 2) * ‖G t‖ₑ := by
      apply lintegral_mono
      intro t
      have hc : ‖(a (t 0) : ℂ) * (b (t 1) : ℂ)‖ₑ ≤ ENNReal.ofReal (C ^ 2) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_endpoint_product_le hC ha hb t)
      change ‖((a (t 0) : ℂ) * (b (t 1) : ℂ)) * G t‖ₑ ≤ _
      rw [enorm_mul]
      exact mul_le_mul' hc le_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The zeroth time moment of a weighted ordered integral is bounded by its amplitude box integral. -/
theorem lintegral_enorm_weightedOrderedIntegral_le {n : ℕ} {a b : ℝ → ℝ} {R C : ℝ}
    (hC : 0 ≤ C) (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (A : (Fin n → ℝ) → ℂ) :
    (∫⁻ t, ‖weightedOrderedIntegral n a b A t‖ₑ) ≤
      ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) ^ 2 * boxIntegral n (fun v => ‖A v‖ₑ) R := by
  apply (lintegral_enorm_endpoint_product_le hC ha hb
    (fun t => orderedIntegral n A (t 0) (t 1))).trans
  calc
    _ ≤ ENNReal.ofReal (C ^ 2) *
        ∫⁻ _t in Icc (fun _ : Fin 2 => -R) (fun _ => R), boxIntegral n (fun v => ‖A v‖ₑ) R := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hp := (mem_two_time_box_iff R t).mp ht
      exact enorm_orderedIntegral_le_boxIntegral n A R (t 0) (t 1) (abs_le.mp hp.1) (abs_le.mp hp.2)
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, volume_two_time_box]
      ring

end WaveTurbulence.Fourier
