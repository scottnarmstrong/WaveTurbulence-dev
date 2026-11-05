/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FactorialStageAbsorption
public import WaveTurbulence.Foundations.XChain.InductWidthRange
/-! The actual N=R^(40d) leaves a quarter-exponent budget for factorial losses. -/
public section
namespace WaveTurbulence.Induct

theorem four_R_quartic_le_N (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ) (hR : 2 ≤ P.R p) :
    4 * P.R p ^ 4 ≤ P.N p := by
  have h2 : 4 ≤ P.R p ^ 2 := by nlinarith
  have h := Nat.mul_le_mul_right (P.R p ^ 4) h2
  have hk : 6 ≤ 40 * P.d := by omega
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ P.R p) hk
  rw [show 6 = 2 + 4 from rfl, pow_add] at hp
  exact h.trans hp

theorem factorial_stage_loss_le_exp_quarter (P : WTParams) (hd : 1 ≤ P.d)
    (p w C : ℕ) (hw : w ≤ 20 * P.R p)
    (hR : 1000 * ((C + 2) ^ 2 + 1) ≤ P.R p) :
    (2 : ℝ) ^ w * (((C + 2) * w).factorial : ℝ) ≤ Real.exp ((P.N p : ℝ) / 4) := by
  have hR2 : 2 ≤ P.R p := by nlinarith
  have hN := four_R_quartic_le_N P hd p hR2
  have hNr : 4 * (P.R p : ℝ) ^ 4 ≤ P.N p := by exact_mod_cast hN
  have h := factorial_stage_loss_le_exp w C (P.R p) (P.R p ^ 4) hw hR le_rfl
  push_cast at h
  exact h.trans (Real.exp_le_exp.mpr (by linarith))

end WaveTurbulence.Induct
