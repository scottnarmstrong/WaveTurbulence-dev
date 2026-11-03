/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Hölder interpolation of time Fourier norms

TARGET `(normX1)`: logarithmic convexity in the time regularity exponent.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

@[fun_prop] theorem timeFourier_continuous {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) : Continuous (timeFourier f) := by
  apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar _ hf
  change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
  fun_prop

private theorem timeWeight_interpolate {r : ℕ} (θ θ' a b : ℝ) (ξ : Fin r → ℝ) :
    timeWeight (a * θ + b * θ') ξ = timeWeight θ ξ ^ a * timeWeight θ' ξ ^ b := by
  unfold timeWeight
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (timeBracket_pos ξ) _),
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (timeBracket_pos ξ) _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (timeBracket_pos ξ).le _) _)]
  congr 1
  rw [← Real.rpow_mul (timeBracket_pos ξ).le, ← Real.rpow_mul (timeBracket_pos ξ).le,
    ← Real.rpow_add (timeBracket_pos ξ)]
  congr 1
  ring

/-- Hölder interpolation, including infinite norm values. Endpoints are
immediate equalities; this theorem states the interior case. -/
theorem timeFourierNorm_interpolate {r : ℕ} (θ θ' : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (f : (Fin r → ℝ) → ℂ) :
    timeFourierNorm (a * θ + (1 - a) * θ') f ≤
      timeFourierNorm θ f ^ a * timeFourierNorm θ' f ^ (1 - a) := by
  classical
  by_cases hf : Integrable f
  · rw [timeFourierNorm_eq_lintegral hf, timeFourierNorm_eq_lintegral hf,
      timeFourierNorm_eq_lintegral hf]
    have hb : 0 < 1 - a := sub_pos.mpr ha1
    let u := fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ
    let v := fun ξ => timeWeight θ' ξ * ‖timeFourier f ξ‖ₑ
    have hu : Measurable u := (timeWeight_measurable θ).mul
      (timeFourier_continuous hf).measurable.enorm
    have hv : Measurable v := (timeWeight_measurable θ').mul
      (timeFourier_continuous hf).measurable.enorm
    have hp := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      (Real.HolderConjugate.inv_one_sub_inv ha ha1)
      (f := fun ξ => u ξ ^ a) (g := fun ξ => v ξ ^ (1 - a))
      (hu.pow_const _).aemeasurable (hv.pow_const _).aemeasurable
    have huEq (ξ : Fin r → ℝ) : (u ξ ^ a) ^ a⁻¹ = u ξ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ha.ne', ENNReal.rpow_one]
    have hvEq (ξ : Fin r → ℝ) : (v ξ ^ (1 - a)) ^ (1 - a)⁻¹ = v ξ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hb.ne', ENNReal.rpow_one]
    simp only [huEq, hvEq, one_div, inv_inv] at hp
    convert hp using 1
    apply lintegral_congr
    intro ξ
    dsimp [u, v]
    rw [timeWeight_interpolate, ENNReal.mul_rpow_of_nonneg _ _ ha.le,
      ENNReal.mul_rpow_of_nonneg _ _ hb.le]
    calc
      _ = (timeWeight θ ξ ^ a * timeWeight θ' ξ ^ (1 - a)) *
          (‖timeFourier f ξ‖ₑ ^ a * ‖timeFourier f ξ‖ₑ ^ (1 - a)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le, add_sub_cancel,
          ENNReal.rpow_one]
      _ = _ := by ac_rfl
  · simp [timeFourierNorm_of_not_integrable hf, ENNReal.top_rpow_of_pos ha,
      ENNReal.top_rpow_of_pos (sub_pos.mpr ha1)]

end WaveTurbulence.Fourier
