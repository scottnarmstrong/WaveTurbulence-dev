/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftEnvelopeExponential
/-! The actual total-order cutoff beats the universal finite graft count. -/
public section
namespace WaveTurbulence.Induct

theorem total_order_tail_cutoff_large {N w : ℕ} (hN : 20 ≤ N) (hw : w ≤ 100 * N) :
    (N : ℝ) ^ 4 / 2 ≤ (((N ^ 4 + 1) - w * N : ℕ) : ℝ) := by
  have hpow : 400 ≤ N ^ 2 := by
    have h := Nat.pow_le_pow_left hN 2
    norm_num at h ⊢
    exact h
  have h4 : 200 * N ^ 2 ≤ N ^ 4 := by
    have h := Nat.mul_le_mul_right (N ^ 2) hpow
    rw [show 4 = 2 + 2 from rfl, pow_add]
    nlinarith
  have hwN : 2 * (w * N) ≤ N ^ 4 := by
    have h := Nat.mul_le_mul_right N hw
    nlinarith
  have hJ : N ^ 4 ≤ 2 * ((N ^ 4 + 1) - w * N) := by omega
  have hr : (N : ℝ) ^ 4 ≤ 2 * (((N ^ 4 + 1) - w * N : ℕ) : ℝ) := by exact_mod_cast hJ
  linarith

theorem envelope_times_total_tail_le_exp {N w : ℕ} (hN : 20 ≤ N) (hw : w ≤ 100 * N)
    {E q : ℝ} (hE : E ≤ Real.exp (1000000 * (N : ℝ) ^ 4))
    (hq : 0 ≤ q) (hq' : q ≤ Real.exp (-4000000)) :
    E * q ^ ((N ^ 4 + 1) - w * N) ≤ Real.exp (-(20 * (N : ℝ))) := by
  let J := (N ^ 4 + 1) - w * N
  have hpow : q ^ J ≤ Real.exp (-4000000 * (J : ℝ)) := by
    have h := pow_le_pow_left₀ hq hq' J
    simpa only [← Real.exp_nat_mul, mul_comm (J : ℝ)] using h
  have hprod := mul_le_mul hE hpow (pow_nonneg hq _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hJ := total_order_tail_cutoff_large hN hw
  have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ N)) (by decide)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact hprod.trans (Real.exp_le_exp.mpr (by dsimp [J] at *; nlinarith))

end WaveTurbulence.Induct
