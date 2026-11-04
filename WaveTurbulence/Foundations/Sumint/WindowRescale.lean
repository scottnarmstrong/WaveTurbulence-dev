/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Rescaling unit time intervals in sumint

The identity uses closed intervals, exactly as in the drafted time
domain. Endpoints have zero Lebesgue measure.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- Positive affine rescaling of a closed unit interval, without an integrability premise. -/
theorem integral_unit_affine (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (q t : ℝ) :
    (∫ s in Icc q (q + 1), f (c * (s - t))) =
      c⁻¹ * ∫ u in Icc (c * (q - t)) (c * (q - t) + c), f u := by
  have hq : q ≤ q + 1 := by linarith
  have hends : c * (q - t) ≤ c * (q - t) + c := by linarith
  have he₁ : c * q + -(c * t) = c * (q - t) := by ring
  have he₂ : c * (q + 1) + -(c * t) = c * (q - t) + c := by ring
  have hf : (fun s => f (c * (s - t))) = fun s => f (c * s + -(c * t)) := by
    funext s
    congr 1
    ring
  rw [hf, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq,
    intervalIntegral.integral_comp_mul_add f hc.ne' (-(c * t)), he₁, he₂,
    intervalIntegral.integral_of_le hends, integral_Icc_eq_integral_Ioc, smul_eq_mul]

end WaveTurbulence.Sumint
