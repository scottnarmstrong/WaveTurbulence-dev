/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! The numerical probability absorption in TARGET S1. -/
public section
namespace WaveTurbulence.Induct

theorem R_succ_relation (P : WTParams) {p : ℕ} (hp : p < P.D) :
    P.R p = P.N (p + 1) ^ (40 * P.d) := by
  change P.Rdown (P.D - p) = (P.Rdown (P.D - (p + 1)) ^ (40 * P.d)) ^ (40 * P.d)
  rw [show P.D - p = P.D - (p + 1) + 1 by omega, WTParams.Rdown]

theorem N_succ_relation (P : WTParams) {p : ℕ} (hp : p < P.D) :
    P.N p = P.N (p + 1) ^ ((40 * P.d) * (40 * P.d)) := by
  rw [WTParams.N, R_succ_relation P hp]
  exact (pow_mul _ _ _).symm

theorem N_succ_gap (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D)
    (hN : 2 ≤ P.N (p + 1)) : 2 * P.N (p + 1) ≤ P.N p := by
  rw [N_succ_relation P hp]
  have he : 2 ≤ (40 * P.d) * (40 * P.d) := by nlinarith
  have hpow : P.N (p + 1) ^ 2 ≤ P.N (p + 1) ^ ((40 * P.d) * (40 * P.d)) :=
    Nat.pow_le_pow_right (by omega) he
  have hsq : 2 * P.N (p + 1) ≤ P.N (p + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right (P.N (p + 1)) hN
  exact hsq.trans hpow

theorem N_ge_two_of_exp_two_le (P : WTParams) (hd : 1 ≤ P.d) (hL : Real.exp 2 ≤ P.L)
    (p : ℕ) : 2 ≤ P.N p := by
  have hL0 : 0 < P.L := (Real.exp_pos 2).trans_le hL
  have hlog : 2 ≤ Real.log P.L := (Real.le_log_iff_exp_le hL0).mpr hL
  have ha : 1 ≤ 40 * P.d := by omega
  have hpow (n : ℕ) (hn : 2 ≤ n) : 2 ≤ n ^ (40 * P.d) := by
    have h := Nat.pow_le_pow_right (by omega : 0 < n) ha
    exact hn.trans (by simpa only [pow_one] using h)
  have hbase : 2 ≤ P.Rdown 0 := by
    change 2 ≤ ⌊Real.log P.L ^ (40 * P.d)⌋₊
    apply Nat.le_floor
    have h := pow_le_pow_right₀ (by linarith : 1 ≤ Real.log P.L) ha
    exact hlog.trans (by simpa only [pow_one] using h)
  have hr (k : ℕ) : 2 ≤ P.Rdown k := by
    induction k with
    | zero => exact hbase
    | succ k ih => exact hpow _ (hpow _ ih)
  exact hpow _ (hr _)

/-- The two deleted probabilities fit into the next step's target tail. -/
theorem exp_tail_step {m n : ℝ} (hn : 1 ≤ n) (hm : 2 * n ≤ m) :
    Real.exp (-m) + Real.exp (-(4 * n)) ≤ Real.exp (-n) := by
  have hn0 : 0 ≤ n := le_trans zero_le_one hn
  have he : 2 ≤ Real.exp n := (by linarith : (2 : ℝ) ≤ n + 1).trans (Real.add_one_le_exp n)
  have hx0 := (Real.exp_pos (-n)).le
  have hx : 2 * Real.exp (-n) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right he hx0
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    exact h
  have hsq : Real.exp (-(2 * n)) = Real.exp (-n) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-(2 * n)) + Real.exp (-(2 * n)) :=
      add_le_add (Real.exp_le_exp.mpr (by linarith)) (Real.exp_le_exp.mpr (by linarith))
    _ = 2 * Real.exp (-(2 * n)) := by ring
    _ ≤ _ := by rw [hsq]; nlinarith [mul_le_mul_of_nonneg_right hx hx0]

/-- Exact scalar absorption needed after the measured fixedpoint extension. -/
theorem probability_step_lower (P : WTParams) (hd : 1 ≤ P.d)
    (hL : Real.exp 2 ≤ P.L) {p : ℕ} (hp : p < P.D) {x : ℝ}
    (hx : 1 - Real.exp (-(P.N p : ℝ)) - Real.exp (-(4 * P.N (p + 1) : ℝ)) ≤ x) :
    1 - Real.exp (-(P.N (p + 1) : ℝ)) ≤ x := by
  have hN := N_ge_two_of_exp_two_le P hd hL (p + 1)
  have hgap := N_succ_gap P hd hp hN
  have hnr : (1 : ℝ) ≤ P.N (p + 1) := by exact_mod_cast (by omega : 1 ≤ P.N (p + 1))
  have hgr : 2 * (P.N (p + 1) : ℝ) ≤ P.N p := by exact_mod_cast hgap
  have ht := exp_tail_step hnr hgr
  linarith

end WaveTurbulence.Induct
