/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.StageOrderGrowth
/-! The actual downward recursion supplies a uniform logarithmic tail threshold at every stage. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

private theorem nat_le_pow_pos (a e : ℕ) (he : e ≠ 0) : a ≤ a ^ e := by
  by_cases ha : a = 0
  · subst a; exact Nat.zero_le _
  · exact le_self_pow₀ (by omega) he

theorem Rdown_zero_le (P : WTParams) (hd : 1 ≤ P.d) (k : ℕ) : P.Rdown 0 ≤ P.Rdown k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    exact ih.trans ((nat_le_pow_pos (P.Rdown k) (40 * P.d) (by omega)).trans
      (nat_le_pow_pos _ (40 * P.d) (by omega)))

theorem floor_log_pow_le_N (P : WTParams) (hd : 1 ≤ P.d) (q : ℕ) :
    ⌊Real.log P.L ^ (40 * P.d)⌋₊ ≤ P.N q :=
  (Rdown_zero_le P hd (P.D - q)).trans (nat_le_pow_pos _ (40 * P.d) (by omega))

theorem log_sq_sub_one_le_N (P : WTParams) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L)
    (q : ℕ) : Real.log P.L ^ 2 - 1 ≤ (P.N q : ℝ) := by
  have hp : Real.log P.L ^ 2 ≤ Real.log P.L ^ (40 * P.d) :=
    pow_le_pow_right₀ hlog (by omega)
  have hf := Nat.sub_one_lt_floor (Real.log P.L ^ (40 * P.d))
  have hN : (⌊Real.log P.L ^ (40 * P.d)⌋₊ : ℝ) ≤ P.N q := by
    exact_mod_cast floor_log_pow_le_N P hd q
  linarith

/-- Above the full-carrier cutoff, every stage exceeds any fixed logarithmic threshold
once log L ≥ 2B+1. This includes the intermediate truncated range. -/
theorem tail_order_ge_log (P : WTParams) (hd : 1 ≤ P.d) (B : ℝ) (hB : 0 ≤ B)
    (hlog : 2 * B + 1 ≤ Real.log P.L) (q n : ℕ) (hn : P.N q < 2 * n) :
    B * Real.log P.L ≤ (n : ℝ) := by
  have hlog1 : 1 ≤ Real.log P.L := by linarith
  have hN := log_sq_sub_one_le_N P hd hlog1 q
  have hn' : (P.N q : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hn
  have hm := mul_nonneg (show 0 ≤ Real.log P.L by linarith)
    (show 0 ≤ Real.log P.L - (2 * B + 1) by linarith)
  nlinarith

end WaveTurbulence.LGSpine
