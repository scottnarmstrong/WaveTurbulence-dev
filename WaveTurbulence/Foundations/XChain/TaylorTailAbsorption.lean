/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RemainderScaleAbsorption
/-! A quartic Taylor cutoff is smaller than half the prescribed spatial remainder scale. -/
public section
namespace WaveTurbulence.Induct

theorem geometric_taylor_tail_le_half_power {N M : ℕ} {L θ A r : ℝ}
    (hN : 4 ≤ N) (hM : N ^ 4 ≤ 2 * M) (hL : 0 < L)
    (hθ : 0 ≤ θ) (hθN : θ ≤ N) (hlog : Real.log L ≤ N)
    (hA : 0 ≤ A) (hAe : A ≤ Real.exp N) (hr : 0 ≤ r) (hre : r ≤ Real.exp (-1)) :
    A * r ^ M ≤ (1 / 2) * L ^ (-θ) := by
  have hp : r ^ M ≤ Real.exp (-(M : ℝ)) := by
    have h := pow_le_pow_left₀ hr hre M
    simpa only [← Real.exp_nat_mul, mul_neg, mul_one] using h
  have hprod := mul_le_mul hAe hp (pow_nonneg hr _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (N : ℝ) ^ 4 ≤ 2 * M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN2 : 4 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ) - 4 by linarith) hN0]
  have hquartic : 2 * ((N : ℝ) ^ 2 + N + 1) ≤ (N : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 2)]
  have hθlog : θ * Real.log L ≤ (N : ℝ) ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hlog hθ).trans
      (by simpa only [pow_two] using mul_le_mul_of_nonneg_right hθN hN0)
  have hexp : (N : ℝ) - M ≤ -1 + Real.log L * (-θ) := by nlinarith
  have he : Real.exp (-1 + Real.log L * (-θ)) = Real.exp (-1) * L ^ (-θ) := by
    rw [Real.exp_add, Real.rpow_def_of_pos hL]
  exact hprod.trans ((Real.exp_le_exp.mpr hexp).trans
    (he.trans_le (mul_le_mul_of_nonneg_right exp_neg_one_le_half (Real.rpow_nonneg hL.le _))))

end WaveTurbulence.Induct
