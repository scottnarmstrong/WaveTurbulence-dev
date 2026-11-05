/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.StageFactorialQuarter
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Explicit exponential budgets for S6, S7, and the finite sum of induction errors. -/
public section
namespace WaveTurbulence.Induct

theorem sqrt_deleted_probability_bound {x N : ℝ} (hx : x ≤ Real.exp (-(4 * N))) :
    Real.sqrt x ≤ Real.exp (-(2 * N)) := by
  have he : Real.exp (-(4 * N)) = Real.exp (-(2 * N)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact (Real.sqrt_le_sqrt hx).trans_eq (he ▸ Real.sqrt_sq (Real.exp_pos _).le)

theorem event_change_budget {x N K : ℝ} (hx : x ≤ Real.exp (-(4 * N)))
    (hK : 0 ≤ K) (hKexp : K ≤ Real.exp (N / 4)) :
    Real.sqrt x * K ≤ Real.exp (-(7 / 4 * N)) := by
  have h := mul_le_mul (sqrt_deleted_probability_bound hx) hKexp hK (Real.exp_pos _).le
  apply h.trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem remainder_cumulant_budget {N K : ℝ} (hK : K ≤ Real.exp (N / 4)) :
    Real.exp (-(10 * N)) * K ≤ Real.exp (-(39 / 4 * N)) := by
  apply (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem five_errors_budget {N : ℝ} (hN : 4 ≤ N) :
    5 * Real.exp (-(7 / 4 * N)) ≤ Real.exp (-N) := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h3 : (6 : ℝ) ≤ Real.exp 3 := by
    have h := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add] at h
    norm_num at h ⊢
    exact h
  have hN3 : (3 : ℝ) ≤ 3 / 4 * N := by linarith
  have hexp : (5 : ℝ) ≤ Real.exp (3 / 4 * N) :=
    (by norm_num : (5 : ℝ) ≤ 6).trans (h3.trans (Real.exp_le_exp.mpr hN3))
  apply (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end WaveTurbulence.Induct
