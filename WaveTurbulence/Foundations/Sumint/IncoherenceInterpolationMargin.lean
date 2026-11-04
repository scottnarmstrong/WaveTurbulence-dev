/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.InterpolationMargins
import Mathlib.Tactic

/-!
# Retaining the weakened incoherence gain after interpolation

A negative-endpoint gain `β/20` suffices. Requiring `40 sqrt η ≤ 1`
reserves the factor lost to interpolation; the stronger full-β source
intermediate estimate is unnecessary for the drafted conclusion.
-/

public section

namespace WaveTurbulence.Sumint

/-- The negative endpoint keeps at least half its interpolation weight. -/
theorem interpolationWeight_le_half {η : ℝ} (hη : 0 ≤ η) (hsmall : 24*η^8 ≤ 1) :
    interpolationWeight η ≤ 1/2 := by
  have h8 : 8*η^8 ≤ 1 := by nlinarith [pow_nonneg hη 8]
  have hw := (interpolationWeight_bounds hη h8).2.2
  linarith

/-- Even the weakened incoherence gain survives interpolation to the exact target exponent. -/
theorem incoherence_gain_after_interpolation {η : ℝ} (hη : 0 ≤ η)
    (hsmall : 24*η^8 ≤ 1) (hsqrt : 40*Real.sqrt η ≤ 1) :
    η^8 ≤ (1-interpolationWeight η)*(partitionExponent η/20) := by
  have hw := interpolationWeight_le_half hη hsmall
  have hb : 0 ≤ partitionExponent η := mul_nonneg (pow_nonneg hη _) (Real.sqrt_nonneg _)
  have hs := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg η)
  rw [mul_assoc, Real.mul_self_sqrt hη] at hs
  have ht := mul_le_mul_of_nonneg_left hs (pow_nonneg hη 7)
  have hw' := mul_le_mul_of_nonneg_right hw hb
  unfold partitionExponent at *
  nlinarith only [ht,hw']

end WaveTurbulence.Sumint
