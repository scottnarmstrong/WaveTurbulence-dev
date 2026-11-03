/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BracketIntegrability
import Mathlib.Tactic

/-!
# An integrable pair envelope for three inverse brackets

The elementary cubic arithmetic-geometric-mean inequality dominates the
three-bracket product by a sum of products of two bracket powers `9/8`.
Each pair is integrable in independent frequency coordinates.
-/

public section

namespace WaveTurbulence.Fourier

/-- A coarse cubic arithmetic-geometric-mean inequality with constant one. -/
theorem mul_three_le_sum_cubes {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u * v * w ≤ u ^ 3 + v ^ 3 + w ^ 3 := by
  have h := mul_nonneg (show 0 ≤ u + v + w by positivity)
    (show 0 ≤ (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 by positivity)
  nlinarith [show 0 ≤ u ^ 3 by positivity, show 0 ≤ v ^ 3 by positivity,
    show 0 ≤ w ^ 3 by positivity]

private theorem cube_rpow_three_eighths {A : ℝ} (hA : 0 < A) :
    (A ^ (-(3 / 8 : ℝ))) ^ 3 = A ^ (-(9 / 8 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
  congr 1
  norm_num

/-- Three inverse three-quarter powers are dominated by integrable pair powers. -/
theorem inverse_three_brackets_le_pairs {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    (A * B * C) ^ (-(3 / 4 : ℝ)) ≤
      A ^ (-(9 / 8 : ℝ)) * B ^ (-(9 / 8 : ℝ)) +
      A ^ (-(9 / 8 : ℝ)) * C ^ (-(9 / 8 : ℝ)) +
      B ^ (-(9 / 8 : ℝ)) * C ^ (-(9 / 8 : ℝ)) := by
  let u := A ^ (-(3 / 8 : ℝ)) * B ^ (-(3 / 8 : ℝ))
  let v := A ^ (-(3 / 8 : ℝ)) * C ^ (-(3 / 8 : ℝ))
  let w := B ^ (-(3 / 8 : ℝ)) * C ^ (-(3 / 8 : ℝ))
  have hprod : u * v * w = (A * B * C) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.mul_rpow (mul_pos hA hB).le hC.le, Real.mul_rpow hA.le hB.le]
    have hpow (X : ℝ) (hX : 0 < X) :
        X ^ (-(3 / 8 : ℝ)) * X ^ (-(3 / 8 : ℝ)) = X ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_add hX]
      congr 1
      norm_num
    dsimp [u, v, w]
    calc
      _ = (A ^ (-(3 / 8 : ℝ)) * A ^ (-(3 / 8 : ℝ))) *
        (B ^ (-(3 / 8 : ℝ)) * B ^ (-(3 / 8 : ℝ))) *
        (C ^ (-(3 / 8 : ℝ)) * C ^ (-(3 / 8 : ℝ))) := by ring
      _ = _ := by rw [hpow A hA, hpow B hB, hpow C hC]
  have hcubes := mul_three_le_sum_cubes
    (show 0 ≤ u by dsimp [u]; positivity) (show 0 ≤ v by dsimp [v]; positivity)
    (show 0 ≤ w by dsimp [w]; positivity)
  rw [hprod] at hcubes
  simpa only [u, v, w, mul_pow, cube_rpow_three_eighths hA,
    cube_rpow_three_eighths hB, cube_rpow_three_eighths hC] using hcubes

/-- A quarter-order weight is absorbed by the three brackets and the pair envelope. -/
theorem weighted_inverse_three_brackets_le_pairs {A B C M : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hM : 0 ≤ M) (hbound : M ≤ A * B * C) :
    M ^ (1 / 4 : ℝ) / (A * B * C) ≤
      A ^ (-(9 / 8 : ℝ)) * B ^ (-(9 / 8 : ℝ)) +
      A ^ (-(9 / 8 : ℝ)) * C ^ (-(9 / 8 : ℝ)) +
      B ^ (-(9 / 8 : ℝ)) * C ^ (-(9 / 8 : ℝ)) := by
  have hp := mul_pos (mul_pos hA hB) hC
  calc
    _ ≤ (A * B * C) ^ (1 / 4 : ℝ) / (A * B * C) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hM hbound (by norm_num)) hp.le
    _ = (A * B * C) ^ (-(3 / 4 : ℝ)) := by
      calc
        _ = (A * B * C) ^ (1 / 4 : ℝ) / (A * B * C) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (A * B * C) ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hp _ _).symm
        _ = _ := by congr 1; norm_num
    _ ≤ _ := inverse_three_brackets_le_pairs hA hB hC

end WaveTurbulence.Fourier
