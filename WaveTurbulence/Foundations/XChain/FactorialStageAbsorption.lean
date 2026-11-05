/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FactorialMomentAbsorption
/-! The factorial conversion loss is absorbed by the stage exponent at sufficiently large root range. -/
public section
namespace WaveTurbulence.Induct

theorem factorial_stage_loss_le_exp (w C R N : ℕ) (hw : w ≤ 20 * R)
    (hR : 1000 * ((C + 2) ^ 2 + 1) ≤ R) (hN : R ^ 4 ≤ N) :
    (2 : ℝ) ^ w * (((C + 2) * w).factorial : ℝ) ≤ Real.exp (N : ℝ) := by
  have hRreal : 1000 * (((C : ℝ) + 2) ^ 2 + 1) ≤ R := by exact_mod_cast hR
  have hwreal : (w : ℝ) ≤ 20 * R := by exact_mod_cast hw
  have hRone : (1 : ℝ) ≤ R := by nlinarith [sq_nonneg ((C : ℝ) + 2)]
  have hAw : ((C : ℝ) + 2) * w ≤ 20 * ((C : ℝ) + 2) * R := by
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ((C : ℝ) + 2) * w) hAw 2
  have hR2 : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hconst : 400 * ((C : ℝ) + 2) ^ 2 + 60 ≤ R := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hconst (sq_nonneg (R : ℝ))
  have hpoly : 2 * (w : ℝ) + (((C + 2) * w : ℕ) : ℝ) ^ 2 + 1 * w ≤ (R : ℝ) ^ 3 := by
    push_cast
    nlinarith
  have h34 : (R : ℝ) ^ 3 ≤ (R : ℝ) ^ 4 := by
    exact pow_le_pow_right₀ hRone (by omega)
  have hNN : (R : ℝ) ^ 4 ≤ N := by exact_mod_cast hN
  have h := factorial_moment_loss_le_exp w C 1 zero_le_one
  simpa only [one_pow, mul_one] using h.trans (Real.exp_le_exp.mpr (hpoly.trans (h34.trans hNN)))

end WaveTurbulence.Induct
