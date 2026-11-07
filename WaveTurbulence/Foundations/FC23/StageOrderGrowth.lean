/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.WTParamsN
/-! TARGET L2253: every permitted order is bounded by a fixed power of log L. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FC23

/-- The precise downwards-recursion exponent for Rdown. -/
theorem Rdown_le_log_pow (P : WTParams) (k : ℕ) :
    (P.Rdown k : ℝ) ≤ Real.log P.L ^ ((40 * P.d) ^ (2 * k + 1)) := by
  induction k with
  | zero =>
    have hnon : 0 ≤ Real.log P.L ^ (40 * P.d) := by
      rw [show 40 * P.d = 2 * (20 * P.d) by omega, pow_mul]
      positivity
    simpa only [WTParams.Rdown, Nat.mul_zero, Nat.zero_add, pow_one] using Nat.floor_le hnon
  | succ k ih =>
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (P.Rdown k)) ih ((40 * P.d) * (40 * P.d))
    have he : (40 * P.d) ^ (2 * (k + 1) + 1) = (40 * P.d) ^ (2 * k + 1) * ((40 * P.d) * (40 * P.d)) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add, pow_two]
    simp only [WTParams.Rdown, Nat.cast_pow, ← pow_mul]
    rw [he]
    simpa only [← pow_mul] using h

/-- One exponent, independent of L and p, controls the complete quartic order range. -/
theorem N_quartic_le_log_pow (P : WTParams) (hd : 1 ≤ P.d)
    (hlog : 1 ≤ Real.log P.L) (p : ℕ) :
    (P.N p : ℝ) ^ 4 ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
  have hr := pow_le_pow_left₀ (Nat.cast_nonneg (P.Rdown (P.D - p)))
    (Rdown_le_log_pow P (P.D - p)) ((40 * P.d) * 4)
  have he : (40 * P.d) ^ (2 * (P.D - p) + 1) * ((40 * P.d) * 4) =
      4 * (40 * P.d) ^ (2 * (P.D - p) + 2) := by
    rw [show 2 * (P.D - p) + 2 = (2 * (P.D - p) + 1) + 1 by omega, pow_succ]
    ring
  have hN : (P.N p : ℝ) ^ 4 ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * (P.D - p) + 2)) := by
    simpa only [WTParams.N, WTParams.R, Nat.cast_pow, ← pow_mul, he] using hr
  exact hN.trans (pow_le_pow_right₀ hlog (Nat.mul_le_mul_left 4
    (Nat.pow_le_pow_right (by omega : 0 < 40 * P.d) (by omega))))

end WaveTurbulence.FC23
