/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductLogSize
public import WaveTurbulence.Foundations.XChain.GraftEnvelopeExponential
/-! The lattice factor in the explicit envelope satisfies the required square-exponential size bound. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def baseLatticeSum (d : ℕ) : ℝ :=
  ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹

theorem lattice_weight_sum_le_exp_square {d N : ℕ} (L b : ℝ) (hL : 1 ≤ L)
    (hb : (d : ℝ) + 1 ≤ b) (hlog : Real.log L ≤ N)
    (hbase : baseLatticeSum d ≤ L) (hN : 2 * d + 4 ≤ N) :
    (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ≤ Real.exp ((N : ℝ) ^ 2) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLe : L ≤ Real.exp N := by
    rw [← Real.exp_log hL0]
    exact Real.exp_le_exp.mpr hlog
  have hsum : (∑' m : Fin d → ℤ, jbr (latticePoint L m) ^ (-b)) ≤ latSum d L := by
    apply (summable_lattice_bracket_weight L b hL hb).tsum_le_tsum
      (fun m => Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (neg_le_neg hb))
      (summable_jbr_rpow_neg hL)
  have hbase0 : 0 ≤ baseLatticeSum d := tsum_nonneg (fun m => by positivity)
  have hsqrt : Real.sqrt 2 ≤ Real.exp 1 := by
    have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    exact hs.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hscale : Real.sqrt 2 * L ≤ Real.exp (1 + (N : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul hsqrt hLe hL0.le (Real.exp_pos _).le
  have hpow : (Real.sqrt 2 * L) ^ (d + 1) ≤ Real.exp (((N : ℝ) + 1) * (d + 1)) := by
    have h := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg 2) hL0.le) hscale (d + 1)
    simpa only [← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ) (N : ℝ),
      mul_comm ((d : ℝ) + 1)] using h
  have hprod := mul_le_mul hpow (hbase.trans hLe) hbase0 (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hNr : 2 * (d : ℝ) + 4 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by decide)
  have hmul := mul_le_mul_of_nonneg_right (show (d : ℝ) + 2 ≤ (N : ℝ) / 2 by linarith) hN0
  have hexp : ((N : ℝ) + 1) * (d + 1) + N ≤ (N : ℝ) ^ 2 := by nlinarith
  exact hsum.trans ((latSum_le hL).trans (hprod.trans (Real.exp_le_exp.mpr hexp)))

end WaveTurbulence.Induct
