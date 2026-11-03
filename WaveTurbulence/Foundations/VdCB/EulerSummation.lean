/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.EulerCell
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sharp Euler summation on an integer interval

The sum `∑_{a≤n<b} F(n+1)` is exactly the convention `a<n≤b`.
The endpoint correction is displayed explicitly. The sawtooth derivative
integral is proved integrable by its finite cell decomposition.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

private theorem intervalIntegrable_sawtooth_mul_deriv_cell {F : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F) (n : ℕ) :
    IntervalIntegrable (fun x => (sawtooth x : ℂ) * deriv F x) volume (n : ℝ) ((n : ℝ) + 1) := by
  have hc : Continuous (fun x : ℝ => ((x - n - 1 / 2 : ℝ) : ℂ) * deriv F x) := by
    have hd := hF.continuous_deriv_one
    fun_prop
  apply (hc.intervalIntegrable (n : ℝ) ((n : ℝ) + 1)).congr_uIoo
  intro x hx
  rw [uIoo_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hx
  have he := sawtooth_eq_on_cell (n : ℤ) (by simpa only [Int.cast_natCast] using hx)
  dsimp only
  rw [he, Int.cast_natCast]

/-- Integrability of the actual sawtooth remainder in the finite Euler formula. -/
theorem intervalIntegrable_sawtooth_mul_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    {a b : ℕ} (hab : a ≤ b) :
    IntervalIntegrable (fun x => (sawtooth x : ℂ) * deriv F x) volume (a : ℝ) (b : ℝ) := by
  apply IntervalIntegrable.trans_iterate_Ico (a := fun n : ℕ => (n : ℝ)) hab
  intro k hk
  simpa only [Nat.cast_add, Nat.cast_one] using intervalIntegrable_sawtooth_mul_deriv_cell hF k

/-- First-order Euler summation, with the exact half-open endpoint correction. -/
theorem euler_summation {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b, F ((n : ℝ) + 1)) =
      (∫ x in (a : ℝ)..(b : ℝ), F x) +
        (∫ x in (a : ℝ)..(b : ℝ), (sawtooth x : ℂ) * deriv F x) + (F b - F a) / 2 := by
  induction b, hab using Nat.le_induction with
  | base => simp only [Finset.Ico_self, Finset.sum_empty, intervalIntegral.integral_same,
      sub_self, zero_div, add_zero]
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, Nat.cast_add, Nat.cast_one]
      have hFint := intervalIntegral.integral_add_adjacent_intervals
        (hF.continuous.intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ))
        (hF.continuous.intervalIntegrable (μ := volume) (b : ℝ) ((b : ℝ) + 1))
      have hψint := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_sawtooth_mul_deriv hF hab)
        (intervalIntegrable_sawtooth_mul_deriv_cell hF b)
      rw [← hFint, ← hψint]
      have hcell := integral_sawtooth_mul_deriv_cell hF (b : ℤ)
      simp only [Int.cast_natCast] at hcell
      linear_combination ih - hcell

end WaveTurbulence.VdCB
