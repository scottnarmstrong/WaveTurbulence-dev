/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BracketIntegrability
public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import WaveTurbulence.Foundations.Fourier.TwoCoordinateIntegration
import Mathlib.Tactic

/-!
# An integrable envelope at every negative time regularity

Splitting the negative power of the maximum bracket equally between the
coordinates avoids a logarithmic endpoint in TARGET A.2's triangular estimate.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Fourier

/-- The product envelope for negative regularity `-η`. -/
@[expose] noncomputable def negativeFrequencyEnvelope (η : ℝ) (ξ : Fin 2 → ℝ) : ℝ :=
  inverseBracketPower (1 + η / 2) (ξ 0) * inverseBracketPower (1 + η / 2) (ξ 1)

/-- Nonnegativity of the envelope. -/
theorem negativeFrequencyEnvelope_nonneg (η : ℝ) (ξ : Fin 2 → ℝ) :
    0 ≤ negativeFrequencyEnvelope η ξ :=
  mul_nonneg (inverseBracketPower_nonneg _ _) (inverseBracketPower_nonneg _ _)

/-- Its integrability needs exactly positive `η`. -/
theorem negativeFrequencyEnvelope_integrable {η : ℝ} (hη : 0 < η) :
    Integrable (negativeFrequencyEnvelope η) := by
  have hq : 1 < 1 + η / 2 := by linarith
  exact (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable
    (integrable_inverseBracketPower_product hq hq)

/-- The maximum-bracket weight pays for integrability in both coordinates. -/
theorem negative_weight_two_brackets_le {η : ℝ} (hη : 0 ≤ η) (ξ : Fin 2 → ℝ) :
    timeBracket ξ ^ (-η) /
      (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2)) ≤
      negativeFrequencyEnvelope η ξ := by
  let a := Real.sqrt (1 + (ξ 0) ^ 2)
  let b := Real.sqrt (1 + (ξ 1) ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have he : -η = -η / 2 + -η / 2 := by ring
  have h0 : timeBracket ξ ^ (-η / 2) ≤ a ^ (-η / 2) :=
    Real.rpow_le_rpow_of_nonpos ha (bracket_le_timeBracket ξ 0) (by linarith)
  have h1 : timeBracket ξ ^ (-η / 2) ≤ b ^ (-η / 2) :=
    Real.rpow_le_rpow_of_nonpos hb (bracket_le_timeBracket ξ 1) (by linarith)
  have hh : timeBracket ξ ^ (-η) ≤ a ^ (-η / 2) * b ^ (-η / 2) := by
    calc
      _ = timeBracket ξ ^ (-η / 2) * timeBracket ξ ^ (-η / 2) := by
        calc
          _ = timeBracket ξ ^ (-η / 2 + -η / 2) := congrArg (fun e : ℝ => timeBracket ξ ^ e) he
          _ = _ := Real.rpow_add (timeBracket_pos ξ) _ _
      _ ≤ _ := mul_le_mul h0 h1 (Real.rpow_nonneg (timeBracket_pos ξ).le _)
        (Real.rpow_nonneg ha.le _)
  calc
    _ ≤ (a ^ (-η / 2) * b ^ (-η / 2)) / (a * b) :=
      div_le_div_of_nonneg_right hh (mul_pos ha hb).le
    _ = negativeFrequencyEnvelope η ξ := by
      unfold negativeFrequencyEnvelope inverseBracketPower
      change _ = a ^ (-(1 + η / 2)) * b ^ (-(1 + η / 2))
      have hx : -(1 + η / 2) = -η / 2 - 1 := by ring
      rw [hx, Real.rpow_sub ha, Real.rpow_sub hb, Real.rpow_one, Real.rpow_one]
      ring

end WaveTurbulence.Fourier
