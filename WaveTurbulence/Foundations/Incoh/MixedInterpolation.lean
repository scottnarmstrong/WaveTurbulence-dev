/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import WaveTurbulence.Foundations.Fourier.TimeInterpolation

/-!
# Mixed-norm interpolation for incoherent tree kernels

TARGET (incohproof26)–(incohproof28): the vector supremum remains inside
the Fourier integral, including arbitrary vector-dependent phases.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

open WaveTurbulence.Fourier

private theorem incoh_timeWeight_interpolate {r : ℕ} (θ θ' a b : ℝ) (ξ : Fin r → ℝ) :
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

/-- Hölder interpolation with the momentum supremum inside the frequency integral. -/
theorem mixedFourierNorm00_interpolate {r : ℕ} {V : Type*} (θ θ' : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (F : (Fin r → ℝ) → V → ℂ) :
    mixedFourierNorm00 (a * θ + (1 - a) * θ') F ≤
      mixedFourierNorm00 θ F ^ a * mixedFourierNorm00 θ' F ^ (1 - a) := by
  classical
  by_cases hf : ∀ v, Integrable (fun t => F t v)
  · rw [mixedFourierNorm00_eq_lintegral hf, mixedFourierNorm00_eq_lintegral hf,
      mixedFourierNorm00_eq_lintegral hf]
    have hb : 0 < 1 - a := sub_pos.mpr ha1
    let u := fun ξ => timeWeight θ ξ * mixedFourierEnvelope00 F ξ
    let v := fun ξ => timeWeight θ' ξ * mixedFourierEnvelope00 F ξ
    have hu : Measurable u := (timeWeight_measurable θ).mul
      (measurable_mixedFourierEnvelope00 hf)
    have hv : Measurable v := (timeWeight_measurable θ').mul
      (measurable_mixedFourierEnvelope00 hf)
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
    rw [incoh_timeWeight_interpolate, ENNReal.mul_rpow_of_nonneg _ _ ha.le,
      ENNReal.mul_rpow_of_nonneg _ _ hb.le]
    calc
      _ = (timeWeight θ ξ ^ a * timeWeight θ' ξ ^ (1 - a)) *
          (mixedFourierEnvelope00 F ξ ^ a * mixedFourierEnvelope00 F ξ ^ (1 - a)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le, add_sub_cancel,
          ENNReal.rpow_one]
      _ = _ := by ac_rfl
  · simp [mixedFourierNorm00_of_not_integrable hf, ENNReal.top_rpow_of_pos ha,
      ENNReal.top_rpow_of_pos (sub_pos.mpr ha1)]


end WaveTurbulence.Incoh
