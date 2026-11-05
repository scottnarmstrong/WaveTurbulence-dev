/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeEnvelopeSize
public import WaveTurbulence.Foundations.XChain.GraftInputErrorAbsorption
public import WaveTurbulence.Foundations.XChain.GraftTailAbsorption
/-! The explicit stagewise size hypotheses imply the universal graft-envelope bound. -/
public section
namespace WaveTurbulence.Induct

theorem stage_graftEnvelope_bound (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ)
    (hL : Real.exp 2 ≤ P.L) (C b : ℝ) (hC : 0 ≤ C) (hCL : C ≤ P.L)
    (hb : (P.d : ℝ) + 1 ≤ b) (hbN : b ≤ (P.N (p + 1) : ℝ))
    (hbase : baseLatticeSum P.d ≤ P.L) (hN : 2 * P.d + 4 ≤ P.N (p + 1))
    {w : ℕ} (hw : w ≤ 100 * P.R (p + 1)) :
    graftEnvelope P.d w (P.N (p + 1)) P.L b C ≤
      Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4) := by
  have hLone : 1 ≤ P.L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hL
  have hlog := log_le_N P hd hL (p + 1)
  have hLe : P.L ≤ Real.exp (P.N (p + 1) : ℝ) := by
    rw [← Real.exp_log (zero_lt_one.trans_le hLone)]
    exact Real.exp_le_exp.mpr hlog
  have hwN : w ≤ 100 * P.N (p + 1) :=
    hw.trans (Nat.mul_le_mul_left 100 (R_le_N P hd (p + 1)))
  apply graftEnvelope_le_exp_quartic P.d w (P.N (p + 1)) P.L b C (by omega) hwN
    (by
      have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      linarith) hbN hC (hCL.trans hLe)
  exact lattice_weight_sum_le_exp_square P.L b hLone hb hlog hbase hN

end WaveTurbulence.Induct
