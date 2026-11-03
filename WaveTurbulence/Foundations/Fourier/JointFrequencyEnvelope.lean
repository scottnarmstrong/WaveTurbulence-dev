/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.JointBracketAlgebra
public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic

/-!
# Integrable envelope for the quarter-weighted joint frequency decay

Each term contains two independent frequency coordinates, with bracket
exponent `9/8 > 1`. The two shears involving `ξ₀ + ξ₁` preserve Lebesgue
measure. This closes the frequency integration in TARGET A.3.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Fourier

/-- A sum of three integrable pair envelopes for the time frequencies and their sum. -/
@[expose] noncomputable def jointFrequencyEnvelope (z : ℝ × ℝ) : ℝ :=
  inverseBracketPower (9 / 8) z.1 * inverseBracketPower (9 / 8) z.2 +
  inverseBracketPower (9 / 8) z.1 * inverseBracketPower (9 / 8) (z.1 + z.2) +
  inverseBracketPower (9 / 8) z.2 * inverseBracketPower (9 / 8) (z.1 + z.2)

/-- Nonnegativity of the envelope. -/
theorem jointFrequencyEnvelope_nonneg (z : ℝ × ℝ) : 0 ≤ jointFrequencyEnvelope z := by
  have ha := inverseBracketPower_nonneg (9 / 8) z.1
  have hb := inverseBracketPower_nonneg (9 / 8) z.2
  have hc := inverseBracketPower_nonneg (9 / 8) (z.1 + z.2)
  unfold jointFrequencyEnvelope
  positivity

/-- The joint envelope is integrable over the two real frequency coordinates. -/
theorem jointFrequencyEnvelope_integrable : Integrable jointFrequencyEnvelope := by
  have hbase := integrable_inverseBracketPower_product (p := (9 / 8 : ℝ))
    (q := (9 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hleft : Integrable (fun z : ℝ × ℝ => inverseBracketPower (9 / 8) z.1 *
      inverseBracketPower (9 / 8) (z.1 + z.2)) := by
    exact (measurePreserving_prod_add volume volume).integrable_comp_of_integrable hbase
  have hright : Integrable (fun z : ℝ × ℝ => inverseBracketPower (9 / 8) z.2 *
      inverseBracketPower (9 / 8) (z.1 + z.2)) := by
    exact (measurePreserving_prod_add_swap_right volume volume).integrable_comp_of_integrable hbase
  exact (hbase.add hleft).add hright

private theorem one_le_scalarBracket (x : ℝ) : 1 ≤ Real.sqrt (1 + x ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + x ^ 2)
  nlinarith [sq_nonneg x]

/-- The quarter-weighted three-bracket decay has the explicit integrable envelope. -/
theorem quarter_weight_three_brackets_le_envelope (ξ : Fin 2 → ℝ) :
    timeBracket ξ ^ (1 / 4 : ℝ) /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2) *
        Real.sqrt (1 + (ξ 0 + ξ 1) ^ 2)) ≤ jointFrequencyEnvelope (ξ 0, ξ 1) := by
  let A := Real.sqrt (1 + (ξ 0) ^ 2)
  let B := Real.sqrt (1 + (ξ 1) ^ 2)
  let C := Real.sqrt (1 + (ξ 0 + ξ 1) ^ 2)
  have hA : 1 ≤ A := one_le_scalarBracket _
  have hB : 1 ≤ B := one_le_scalarBracket _
  have hC : 1 ≤ C := one_le_scalarBracket _
  have hAB : 1 ≤ A * B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hABC : 1 ≤ A * B * C := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hC)]
  have hABle : A * B ≤ A * B * C := by
    nlinarith [mul_nonneg (show 0 ≤ A * B by positivity) (sub_nonneg.mpr hC)]
  have hAa : A ≤ A * B := by nlinarith [mul_nonneg (show 0 ≤ A by positivity) (sub_nonneg.mpr hB)]
  have hBb : B ≤ A * B := by nlinarith [mul_nonneg (show 0 ≤ B by positivity) (sub_nonneg.mpr hA)]
  have hM : timeBracket ξ ≤ A * B * C := by
    apply timeBracket_le hABC
    intro j
    fin_cases j
    · change A ≤ A * B * C
      exact hAa.trans hABle
    · change B ≤ A * B * C
      exact hBb.trans hABle
  exact weighted_inverse_three_brackets_le_pairs (by positivity : 0 < A)
    (by positivity : 0 < B) (by positivity : 0 < C) (timeBracket_pos ξ).le hM

/-- Integrability of the envelope in the coordinate-time frequency space. -/
theorem jointFrequencyEnvelope_coordinates_integrable :
    Integrable (fun ξ : Fin 2 → ℝ => jointFrequencyEnvelope (ξ 0, ξ 1)) :=
  (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable jointFrequencyEnvelope_integrable

end WaveTurbulence.Fourier
