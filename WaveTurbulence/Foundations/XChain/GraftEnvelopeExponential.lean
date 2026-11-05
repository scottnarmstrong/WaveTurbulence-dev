/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftEnvelope
/-! A universal quartic exponential majorant for the explicit finite graft envelope. -/
public section
namespace WaveTurbulence.Induct

theorem nat_pow_le_exp_mul (a n : ℕ) : (a : ℝ) ^ n ≤ Real.exp ((a : ℝ) * n) := by
  have ha : (a : ℝ) ≤ Real.exp a := (by linarith : (a : ℝ) ≤ a + 1).trans (Real.add_one_le_exp a)
  have h := pow_le_pow_left₀ (Nat.cast_nonneg a) ha n
  simpa only [← Real.exp_nat_mul, mul_comm (n : ℝ) (a : ℝ)] using h

theorem graftEnvelope_le_exp_quartic (d w N : ℕ) (L b C : ℝ)
    (hN : 2 ≤ N) (hw : w ≤ 100 * N) (hb : 0 ≤ b) (hbN : b ≤ N)
    (hC : 0 ≤ C) (hCN : C ≤ Real.exp N)
    (hS : (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ≤ Real.exp ((N : ℝ) ^ 2)) :
    graftEnvelope d w N L b C ≤ Real.exp (1000000 * (N : ℝ) ^ 4) := by
  let H := w * (2 * N + 1)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hwr : (w : ℝ) ≤ 100 * N := by exact_mod_cast hw
  have hH : (H : ℝ) ≤ 300 * (N : ℝ) ^ 2 := by
    have he : (H : ℝ) = (w : ℝ) * (2 * N + 1) := by dsimp [H]; push_cast; rfl
    rw [he]
    nlinarith
  have h1 : ((3 ^ (3 * N + 1) : ℝ) ^ w) ≤ Real.exp (3 * (3 * (N : ℝ) + 1) * w) := by
    rw [← pow_mul]
    have h := nat_pow_le_exp_mul 3 ((3 * N + 1) * w)
    convert h using 1 <;> push_cast <;> ring
  have h2 : ((2 ^ H : ℝ) ^ H) ≤ Real.exp (2 * (H : ℝ) ^ 2) := by
    rw [← pow_mul]
    have h := nat_pow_le_exp_mul 2 (H * H)
    convert h using 1 <;> push_cast <;> ring
  have hbase : 2 * C ≤ Real.exp (2 + (N : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)]) hCN hC (Real.exp_pos _).le
  have h3 : (2 * C) ^ H ≤ Real.exp (((N : ℝ) + 2) * H) := by
    have h := pow_le_pow_left₀ (mul_nonneg (by norm_num) hC) hbase H
    simpa only [← Real.exp_nat_mul, add_comm (2 : ℝ) (N : ℝ), mul_comm (H : ℝ)] using h
  have h4 : (2 ^ H : ℝ) ^ b ≤ Real.exp (2 * (H : ℝ) * b) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ H) (nat_pow_le_exp_mul 2 H) hb
    simpa only [← Real.exp_mul, Nat.cast_ofNat] using h
  have hmax : max 1 (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ≤ Real.exp ((N : ℝ) ^ 2) :=
    max_le (Real.one_le_exp (sq_nonneg _)) hS
  have h5 : (max 1 (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b))) ^ H ≤
      Real.exp ((N : ℝ) ^ 2 * H) := by
    have h := pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax H
    simpa only [← Real.exp_nat_mul, mul_comm (H : ℝ)] using h
  have h12 := mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
  have h34 := mul_le_mul h3 h4 (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have h345 := mul_le_mul h34 h5 (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (by positivity)
  have hbound := mul_le_mul h12 h345 (by positivity) (by positivity)
  change graftEnvelope d w N L b C ≤ _
  refine hbound.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hHsq : (H : ℝ) ^ 2 ≤ 90000 * (N : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ hH0 hH 2
    nlinarith
  have hHN : (H : ℝ) * N ≤ 300 * (N : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hH hNN]
  have hHN2 : (H : ℝ) * (N : ℝ) ^ 2 ≤ 300 * (N : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg (N : ℝ))]
  have hHb : (H : ℝ) * b ≤ (H : ℝ) * N := mul_le_mul_of_nonneg_left hbN hH0
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
  have hN3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
  have htree : 3 * (3 * (N : ℝ) + 1) * w ≤ 1200 * (N : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hwr (by linarith : 0 ≤ 3 * (3 * (N : ℝ) + 1))]
  nlinarith

end WaveTurbulence.Induct
