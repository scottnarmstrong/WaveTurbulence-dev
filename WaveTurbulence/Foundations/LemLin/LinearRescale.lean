/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.LinearEstimate

/-!
# The rescaled lower-momentum-bound estimate

The form used on a unit time interval in TARGET `sumint` case (d). The
normalizing factor is explicit: the `L^(d+1)` bound is divided by the length
`δ L^(2γ)` of the original time interval.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set

/-- FINDINGS F23 in unit-time coordinates, retaining the exact normalization. -/
theorem lemlin_unit_time_lower_bound {d : ℕ} {L δ γ η : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hγη : γ + η ≤ 1)
    (a r ξ : Mom d) (hrlo : L⁻¹ ≤ ‖r‖) (hrhi : ‖r‖ ≤ L ^ (-γ + η)) (τ : ℝ) :
    (∫ u in Icc (0 : ℝ) 1,
      ‖linearLatticeSum L a ((τ + (δ * L ^ (2 * γ)) * u) • r + ξ)‖) ≤
      linearEstimateConstant d * L ^ (d + 1) / (δ * L ^ (2 * γ)) := by
  let T : ℝ := δ * L ^ (2 * γ)
  have hT : 0 < T := mul_pos hδ (Real.rpow_pos_of_pos (by linarith : 0 < L) _)
  let f : ℝ → ℝ := fun s => ‖linearLatticeSum L a (s • r + ξ)‖
  have he := intervalIntegral.smul_integral_comp_mul_add f T τ (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at he
  have heq : T * (∫ u in Icc (0 : ℝ) 1, f (τ + T * u)) =
      ∫ s in Icc τ (τ + T), f s := by
    simp_rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_of_le (show τ ≤ τ + T by linarith)]
    simpa only [add_comm] using he
  apply (le_div_iff₀ hT).mpr
  rw [mul_comm, heq]
  exact lemlin_lower_momentum_bound hL hδ.le hδ1 hγη a r ξ hrlo hrhi τ

end WaveTurbulence.LemLin
