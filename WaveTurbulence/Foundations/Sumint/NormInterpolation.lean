/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Interpolation with the output supremum inside the Fourier integral

The same ambient extension is used at both endpoints. Hölder acts on
its measurable Fourier envelope, retaining the exact order of supremum
and integration in the drafted norm.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

private theorem timeWeight_interpolate {r : ℕ} (θ θ' a b : ℝ) (ξ : Fin r → ℝ) :
    Fourier.timeWeight (a*θ+b*θ') ξ =
      Fourier.timeWeight θ ξ^a * Fourier.timeWeight θ' ξ^b := by
  unfold Fourier.timeWeight
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (Fourier.timeBracket_pos ξ) _),
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (Fourier.timeBracket_pos ξ) _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le _) _)]
  congr 1
  rw [← Real.rpow_mul (Fourier.timeBracket_pos ξ).le,
    ← Real.rpow_mul (Fourier.timeBracket_pos ξ).le,
    ← Real.rpow_add (Fourier.timeBracket_pos ξ)]
  congr 1
  ring

/-- Logarithmic convexity of the exact general-output order-zero mixed Fourier norm. -/
theorem mixedFourierNorm00_interpolate {r : ℕ} {V : Type*} (θ θ' : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (F : (Fin r → ℝ) → V → ℂ) :
    Fourier.mixedFourierNorm00 (a*θ+(1-a)*θ') F ≤
      Fourier.mixedFourierNorm00 θ F^a * Fourier.mixedFourierNorm00 θ' F^(1-a) := by
  classical
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · rw [Fourier.mixedFourierNorm00_eq_lintegral hF,
      Fourier.mixedFourierNorm00_eq_lintegral hF,
      Fourier.mixedFourierNorm00_eq_lintegral hF]
    have hb : 0 < 1-a := sub_pos.mpr ha1
    let u := fun ξ => Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 F ξ
    let v := fun ξ => Fourier.timeWeight θ' ξ * Fourier.mixedFourierEnvelope00 F ξ
    have hu : Measurable u := (Fourier.timeWeight_measurable θ).mul
      (Fourier.measurable_mixedFourierEnvelope00 hF)
    have hv : Measurable v := (Fourier.timeWeight_measurable θ').mul
      (Fourier.measurable_mixedFourierEnvelope00 hF)
    have hp := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      (Real.HolderConjugate.inv_one_sub_inv ha ha1)
      (f := fun ξ => u ξ^a) (g := fun ξ => v ξ^(1-a))
      (hu.pow_const _).aemeasurable (hv.pow_const _).aemeasurable
    have huEq (ξ : Fin r → ℝ) : (u ξ^a)^a⁻¹ = u ξ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ha.ne', ENNReal.rpow_one]
    have hvEq (ξ : Fin r → ℝ) : (v ξ^(1-a))^(1-a)⁻¹ = v ξ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hb.ne', ENNReal.rpow_one]
    simp only [huEq, hvEq, one_div, inv_inv] at hp
    convert hp using 1
    apply lintegral_congr
    intro ξ
    dsimp [u, v]
    rw [timeWeight_interpolate, ENNReal.mul_rpow_of_nonneg _ _ ha.le,
      ENNReal.mul_rpow_of_nonneg _ _ hb.le]
    calc
      _ = (Fourier.timeWeight θ ξ^a * Fourier.timeWeight θ' ξ^(1-a)) *
          (Fourier.mixedFourierEnvelope00 F ξ^a * Fourier.mixedFourierEnvelope00 F ξ^(1-a)) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le, add_sub_cancel, ENNReal.rpow_one]
      _ = _ := by ac_rfl
  · simp [Fourier.mixedFourierNorm00_of_not_integrable hF, ENNReal.top_rpow_of_pos ha,
      ENNReal.top_rpow_of_pos (sub_pos.mpr ha1)]

end WaveTurbulence.Sumint
