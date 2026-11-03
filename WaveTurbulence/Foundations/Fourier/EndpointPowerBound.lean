/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.EndpointL1Bound
public import WaveTurbulence.Foundations.Fourier.IntegralPowerBound
import Mathlib.Tactic

/-!
# Endpoint localization for time power integrals

Cutoff localization works before any root is taken. This permits direct
Tonelli estimates for the two single-coordinate faces of a rectangle.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Two output cutoffs localize every positive power integral to their box. -/
theorem lintegral_enorm_endpoint_product_rpow_le {a b : ℝ → ℝ} {R C p : ℝ}
    (hC : 0 ≤ C) (hp : 0 < p)
    (ha : EndpointCutoffBounds a R C) (hb : EndpointCutoffBounds b R C)
    (G : (Fin 2 → ℝ) → ℂ) :
    (∫⁻ t, ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ ^ p) ≤
      (ENNReal.ofReal (C ^ 2)) ^ p *
        ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), ‖G t‖ₑ ^ p := by
  have hs : support (fun t : Fin 2 → ℝ =>
      ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ ^ p) ⊆
      Icc (fun _ : Fin 2 => -R) (fun _ => R) := by
    intro t ht
    by_contra hn
    change ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ ^ p ≠ 0 at ht
    rw [endpoint_product_eq_zero_outside ha hb t hn, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos hp] at ht
    exact ht rfl
  calc
    _ = ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      ‖(a (t 0) : ℂ) * (b (t 1) : ℂ) * G t‖ₑ ^ p :=
        (setLIntegral_eq_of_support_subset hs).symm
    _ ≤ ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      (ENNReal.ofReal (C ^ 2)) ^ p * ‖G t‖ₑ ^ p := by
      apply lintegral_mono
      intro t
      have hc : ‖(a (t 0) : ℂ) * (b (t 1) : ℂ)‖ₑ ≤ ENNReal.ofReal (C ^ 2) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_endpoint_product_le hC ha hb t)
      change ‖((a (t 0) : ℂ) * (b (t 1) : ℂ)) * G t‖ₑ ^ p ≤
        (ENNReal.ofReal (C ^ 2)) ^ p * ‖G t‖ₑ ^ p
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      exact mul_le_mul' (ENNReal.rpow_le_rpow hc hp.le) le_rfl
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)

end WaveTurbulence.Fourier
