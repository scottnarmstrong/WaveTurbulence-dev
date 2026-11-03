/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Real algebra for the Gauss bound

These elementary inequalities keep polynomial arithmetic separate from the
logarithms, square roots, and exponential sums in the counting argument.
-/

public section

namespace WaveTurbulence.WeylSums

/-- Combine a coarse and an error-sensitive bound for a nonnegative mass. -/
theorem weighted_square_le_of_mass_bounds (X S K q B H : ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hqK : q ≤ K) (hB : 0 ≤ B)
    (hBK : B * q * K ≤ 1) (hH : 1 ≤ H)
    (hX : X ^ 2 ≤ K + 1 + 2 * S)
    (hcoarse : S * q ≤ 1000 * K ^ 2 * H)
    (hrefined : S * q * B ≤ 1000 * H) :
    X ^ 2 * q * (1 + K ^ 2 * B) ≤ 4096 * K ^ 2 * H := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hH0 : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans hH
  have hmass : S * q * (1 + K ^ 2 * B) ≤ 2000 * K ^ 2 * H := by
    have hh := mul_le_mul_of_nonneg_right hrefined (sq_nonneg K)
    nlinarith only [hh, hcoarse]
  have hweight : q * (1 + K ^ 2 * B) ≤ 2 * K := by
    have hh := mul_le_mul_of_nonneg_right hBK hK0
    nlinarith only [hh, hqK]
  have hdiag : (K + 1) * q * (1 + K ^ 2 * B) ≤ 4 * K ^ 2 * H := by
    have hh := mul_le_mul (show K + 1 ≤ 2 * K by linarith only [hK]) hweight
      (by positivity : 0 ≤ q * (1 + K ^ 2 * B)) (by positivity : 0 ≤ 2 * K)
    have hhH := mul_le_mul_of_nonneg_left hH (sq_nonneg K)
    nlinarith only [hh, hhH]
  have hmul := mul_le_mul_of_nonneg_right hX
    (by positivity : 0 ≤ q * (1 + K ^ 2 * B))
  have hnonneg : 0 ≤ K ^ 2 * H := mul_nonneg (sq_nonneg _) hH0
  nlinarith only [hmul, hdiag, hmass, hnonneg]

/-- Convert the weighted square bound to the required denominator with
`1 + K sqrt B`, losing only an absolute factor. -/
theorem bound_of_weighted_square (X K p b H : ℝ)
    (hX : 0 ≤ X) (hK : 0 ≤ K) (hp : 0 < p) (hb : 0 ≤ b) (hH : 1 ≤ H)
    (hbound : X ^ 2 * p ^ 2 * (1 + K ^ 2 * b ^ 2) ≤ 4096 * K ^ 2 * H) :
    X ≤ 128 * K * H / (p * (1 + K * b)) := by
  have hden : 0 < p * (1 + K * b) := mul_pos hp (by positivity)
  have hweight : (1 + K * b) ^ 2 ≤ 2 * (1 + K ^ 2 * b ^ 2) := by
    nlinarith only [sq_nonneg (K * b - 1)]
  have hmul := mul_le_mul_of_nonneg_left hweight
    (mul_nonneg (sq_nonneg X) (sq_nonneg p))
  have hsq : (X * p * (1 + K * b)) ^ 2 ≤ 8192 * K ^ 2 * H := by
    nlinarith only [hmul, hbound]
  have hHsq : H ≤ H ^ 2 := by nlinarith only [hH]
  have hH0 : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans hH
  have hmulH := mul_le_mul_of_nonneg_left hHsq (sq_nonneg K)
  have hKH : 0 ≤ K ^ 2 * H := mul_nonneg (sq_nonneg _) hH0
  have hsq' : (X * p * (1 + K * b)) ^ 2 ≤ (128 * K * H) ^ 2 := by
    nlinarith only [hsq, hmulH, hKH]
  have hlin := (sq_le_sq₀ (by positivity : 0 ≤ X * p * (1 + K * b))
    (by positivity : 0 ≤ 128 * K * H)).mp hsq'
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_assoc] using hlin

end WaveTurbulence.WeylSums
