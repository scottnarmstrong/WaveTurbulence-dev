/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.StageSizeThreshold
/-! Exponential stage errors are smaller than the polynomial spatial remainder scale. -/
public section
namespace WaveTurbulence.Induct

theorem exp_neg_stage_le_scale (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ)
    (hL : Real.exp 2 ≤ P.L) (hR : 1 ≤ P.R p) (hθ : P.theta p ≤ P.R p) :
    Real.exp (-(P.N p : ℝ)) ≤ P.L ^ (-P.theta p) := by
  have hlog := log_le_Rdown P hd hL (P.D - p)
  change Real.log P.L ≤ (P.R p : ℝ) at hlog
  have hLone : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hL
  have hlog0 : 0 ≤ Real.log P.L := Real.log_nonneg hLone
  have hmul := mul_le_mul hθ hlog hlog0 (Nat.cast_nonneg (P.R p))
  have hNr : (P.R p : ℝ) ^ 2 ≤ P.N p := by
    exact_mod_cast (Nat.pow_le_pow_right hR (by omega : 2 ≤ 40 * P.d))
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hLone)]
  apply Real.exp_le_exp.mpr
  nlinarith

end WaveTurbulence.Induct
