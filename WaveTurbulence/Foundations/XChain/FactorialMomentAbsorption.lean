/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftEnvelopeExponential
public import Mathlib.Data.Nat.Factorial.Basic
/-! Elementary quadratic exponential majorants for the explicit moment/cumulant conversion losses. -/
public section
namespace WaveTurbulence.Induct

theorem factorial_le_exp_square (n : ℕ) : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
  have h : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  exact h.trans ((nat_pow_le_exp_mul n n).trans_eq (by congr 1; ring))

theorem factorial_moment_loss_le_exp (w C : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    (2 : ℝ) ^ w * (((C + 2) * w).factorial : ℝ) * B ^ w ≤
      Real.exp (2 * (w : ℝ) + (((C + 2) * w : ℕ) : ℝ) ^ 2 + B * w) := by
  have hpow : B ^ w ≤ Real.exp (B * w) := by
    have hb : B ≤ Real.exp B := (by linarith : B ≤ B + 1).trans (Real.add_one_le_exp B)
    have h := pow_le_pow_left₀ hB hb w
    simpa only [← Real.exp_nat_mul, mul_comm (w : ℝ)] using h
  have h1 := mul_le_mul (nat_pow_le_exp_mul 2 w) (factorial_le_exp_square ((C + 2) * w))
    (Nat.cast_nonneg _) (Real.exp_pos _).le
  have h := mul_le_mul h1 hpow (pow_nonneg hB w) (by positivity)
  simpa only [← Real.exp_add, Nat.cast_ofNat] using h

end WaveTurbulence.Induct
