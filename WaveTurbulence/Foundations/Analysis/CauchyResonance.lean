/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CauchyConvolution

/-!
# Passing resonance decay through a Cauchy envelope

A reciprocal Japanese bracket can be moved to the central frequency at the
cost of the two possible output centres, zero and that frequency.
-/

public section

namespace WaveTurbulence.Analysis

private theorem resonance_weight_algebra {A B Q S : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 < Q) (hS : 0 < S) (hS2 : S ^ 2 = B) (hbound : Q * S ≤ 2 * (A + B)) :
    S⁻¹ * A⁻¹ ≤ 2 * Q⁻¹ * (A⁻¹ + B⁻¹) := by
  have hleft : S⁻¹ * A⁻¹ = 1 / (S * A) := by ring
  have hright : 2 * Q⁻¹ * (A⁻¹ + B⁻¹) = (2 * (A + B)) / (Q * A * B) := by
    field_simp
    ring
  rw [hleft, hright]
  apply (div_le_div_iff₀ (mul_pos hS hA) (mul_pos (mul_pos hQ hA) hB)).mpr
  have hh : Q * B ≤ 2 * (A + B) * S := by
    calc
      Q * B = (Q * S) * S := by rw [← hS2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound hS.le
  have hh' := mul_le_mul_of_nonneg_right hh hA.le
  nlinarith only [hh']

/-- Moving the reciprocal Japanese bracket to the central frequency.
The two terms correspond to the two choices at a branching node in DH21
Lemma 10.2. -/
theorem oscillatoryWeight_mul_cauchyWeight_le (q s : ℝ) :
    oscillatoryWeight s * cauchyWeight (s - q) ≤
      2 * oscillatoryWeight q * (cauchyWeight (s - q) + cauchyWeight s) := by
  have hA : 0 < 1 + (s - q) ^ 2 := by positivity
  have hB : 0 < 1 + s ^ 2 := by positivity
  have hC : 0 < 1 + q ^ 2 := by positivity
  have hS := Real.sq_sqrt hB.le
  have hQ := Real.sq_sqrt hC.le
  have hCQ : 1 + q ^ 2 ≤ 2 * ((1 + (s - q) ^ 2) + (1 + s ^ 2)) := by
    nlinarith only [sq_nonneg (q - 2 * s)]
  have hb : Real.sqrt (1 + q ^ 2) * Real.sqrt (1 + s ^ 2) ≤
      2 * ((1 + (s - q) ^ 2) + (1 + s ^ 2)) := by
    nlinarith only [sq_nonneg (Real.sqrt (1 + q ^ 2) - Real.sqrt (1 + s ^ 2)),
      hS, hQ, hCQ, hA, hB]
  exact resonance_weight_algebra hA hB (Real.sqrt_pos.2 hC) (Real.sqrt_pos.2 hB) hS hb

end WaveTurbulence.Analysis
