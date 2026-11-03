/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.NegativeFrequencyEnvelope
public import WaveTurbulence.Foundations.Fourier.IntegralPowerBound
import Mathlib.Tactic

/-!
# The Hölder multiplier for positive time regularity

For `p = 1 + 3η` and small positive `η`, the product of bracket powers
`η - 1` belongs to `Lᵖ`. This supplies the strict margin needed in A.2
without using the logarithm-defective convolution estimate in its proof.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- The multiplier left after the two endpoint Fourier moments. -/
@[expose] noncomputable def positiveFrequencyEnvelope (η : ℝ) (ξ : Fin 2 → ℝ) : ℝ :=
  inverseBracketPower (1 - η) (ξ 0) * inverseBracketPower (1 - η) (ξ 1)

/-- The envelope is nonnegative. -/
theorem positiveFrequencyEnvelope_nonneg (η : ℝ) (ξ : Fin 2 → ℝ) :
    0 ≤ positiveFrequencyEnvelope η ξ :=
  mul_nonneg (inverseBracketPower_nonneg _ _) (inverseBracketPower_nonneg _ _)

/-- Its power is another product of inverse brackets. -/
theorem positiveFrequencyEnvelope_rpow (η p : ℝ) (ξ : Fin 2 → ℝ) :
    positiveFrequencyEnvelope η ξ ^ p =
      inverseBracketPower ((1 - η) * p) (ξ 0) *
      inverseBracketPower ((1 - η) * p) (ξ 1) := by
  unfold positiveFrequencyEnvelope inverseBracketPower
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  congr 2 <;> ring

/-- The strict power-integrability margin for the source exponent. -/
theorem positiveFrequencyEnvelope_power_integrable {η p : ℝ}
    (h : 1 < (1 - η) * p) :
    Integrable (fun ξ : Fin 2 → ℝ => positiveFrequencyEnvelope η ξ ^ p) := by
  simp_rw [positiveFrequencyEnvelope_rpow]
  exact (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable
    (integrable_inverseBracketPower_product h h)

/-- The finite extended-real Hölder factor. -/
@[expose] noncomputable def positiveFrequencyFactor (η p : ℝ) : ℝ≥0∞ :=
  (∫⁻ ξ : Fin 2 → ℝ, (ENNReal.ofReal (positiveFrequencyEnvelope η ξ)) ^ p) ^ (1 / p)

/-- The Hölder factor is finite whenever the strict integrability margin holds. -/
theorem positiveFrequencyFactor_ne_top {η p : ℝ} (hp : 0 < p)
    (h : 1 < (1 - η) * p) : positiveFrequencyFactor η p ≠ ⊤ := by
  have hi := positiveFrequencyEnvelope_power_integrable h
  have he : (∫⁻ ξ : Fin 2 → ℝ, (ENNReal.ofReal (positiveFrequencyEnvelope η ξ)) ^ p) =
      ∫⁻ ξ : Fin 2 → ℝ, ENNReal.ofReal (positiveFrequencyEnvelope η ξ ^ p) := by
    apply lintegral_congr
    intro ξ
    exact (ENNReal.ofReal_rpow_of_nonneg (positiveFrequencyEnvelope_nonneg η ξ) hp.le)
  unfold positiveFrequencyFactor
  rw [he]
  apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
  have hh := (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral)
  have hn (ξ : Fin 2 → ℝ) : 0 ≤ positiveFrequencyEnvelope η ξ ^ p :=
    Real.rpow_nonneg (positiveFrequencyEnvelope_nonneg η ξ) _
  simpa only [Real.enorm_of_nonneg (hn _)] using hh.ne

/-- A product of the two brackets dominates the maximum bracket. -/
theorem timeBracket_le_two_brackets (ξ : Fin 2 → ℝ) :
    timeBracket ξ ≤ Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2) := by
  have ha : 1 ≤ Real.sqrt (1 + (ξ 0) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (ξ 0)]
  have hb : 1 ≤ Real.sqrt (1 + (ξ 1) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (ξ 1)]
  apply timeBracket_le
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  · intro j
    fin_cases j
    · change Real.sqrt (1 + (ξ 0) ^ 2) ≤ _
      nlinarith [mul_nonneg (show 0 ≤ Real.sqrt (1 + (ξ 0) ^ 2) by positivity) (sub_nonneg.mpr hb)]
    · change Real.sqrt (1 + (ξ 1) ^ 2) ≤ _
      nlinarith [mul_nonneg (show 0 ≤ Real.sqrt (1 + (ξ 1) ^ 2) by positivity) (sub_nonneg.mpr ha)]

/-- The positive maximum weight divided by the endpoint brackets is controlled by the multiplier. -/
theorem positive_weight_two_brackets_le {η : ℝ} (hη : 0 ≤ η) (ξ : Fin 2 → ℝ) :
    timeBracket ξ ^ η /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2)) ≤
      positiveFrequencyEnvelope η ξ := by
  let a := Real.sqrt (1 + (ξ 0) ^ 2)
  let b := Real.sqrt (1 + (ξ 1) ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  calc
    _ ≤ (a * b) ^ η / (a * b) := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (timeBracket_pos ξ).le (timeBracket_le_two_brackets ξ) hη)
      (mul_pos ha hb).le
    _ = positiveFrequencyEnvelope η ξ := by
      unfold positiveFrequencyEnvelope inverseBracketPower
      change _ = a ^ (-(1 - η)) * b ^ (-(1 - η))
      have he : -(1 - η) = η - 1 := by ring
      rw [he, Real.rpow_sub ha, Real.rpow_sub hb, Real.rpow_one, Real.rpow_one,
        Real.mul_rpow ha.le hb.le]
      ring

end WaveTurbulence.Fourier
