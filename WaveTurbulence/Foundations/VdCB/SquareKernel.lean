/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.PSeries

/-!
# Reciprocal-square frequency kernels

A telescoping comparison controls the nonstationary remainder after
integration by parts. The shift may be any nonnegative real number.
-/

public section

namespace WaveTurbulence.VdCB

private theorem inv_sq_le_two_sub {t : ℝ} (ht : 1 ≤ t) :
    1 / t ^ 2 ≤ 2 / t - 2 / (t + 1) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  field_simp
  nlinarith

/-- Summing the square-denominator tail retains decay in its real shift. -/
theorem sum_range_shifted_inv_sq_le {r : ℝ} (hr : 0 ≤ r) (K : ℕ) :
    (∑ j ∈ Finset.range K, 1 / (r + j + 1) ^ 2) ≤
      2 / (r + 1) - 2 / (r + K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have ht : 1 ≤ r + K + 1 := by linarith only [hr, Nat.cast_nonneg (α := ℝ) K]
      have hh := inv_sq_le_two_sub ht
      have heq : r + ((K + 1 : ℕ) : ℝ) + 1 = (r + K + 1) + 1 := by push_cast; ring
      rw [heq]
      linarith only [ih, hh]

/-- Uniform bound on the one-sided nonstationary square kernel. -/
theorem sum_range_shifted_inv_sq_le_two {r : ℝ} (hr : 0 ≤ r) (K : ℕ) :
    (∑ j ∈ Finset.range K, 1 / (r + j + 1) ^ 2) ≤ 2 / (r + 1) := by
  exact (sum_range_shifted_inv_sq_le hr K).trans
    (sub_le_self _ (by positivity))

end WaveTurbulence.VdCB
