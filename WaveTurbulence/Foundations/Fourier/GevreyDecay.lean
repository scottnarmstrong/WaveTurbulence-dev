/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Optimizing Gevrey integration-by-parts bounds

A sequence of factorial moment bounds implies stretched exponential decay.
The constants are explicit, and the proof uses one integer derivative order
near the square root of the frequency.
-/

public section

namespace WaveTurbulence.Fourier

/-- Optimization of `x^n u ≤ C A^n (2n)!`, uniform in every integer `n`.
The rate is `log 4 / (4 sqrt A)` and the prefactor is `4 C`. -/
theorem gevrey_moments_exp_decay {u C A x : ℝ} (hC : 0 ≤ C)
    (hA : 0 < A) (hx : 0 ≤ x)
    (h : ∀ n : ℕ, x ^ n * u ≤ C * A ^ n * (Nat.factorial (2 * n) : ℝ)) :
    u ≤ 4 * C * Real.exp (-(Real.log 4 / (4 * Real.sqrt A)) * Real.sqrt x) := by
  by_cases hx0 : x = 0
  · subst x
    have h0 := h 0
    norm_num only [pow_zero, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one] at h0
    simp only [Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one]
    linarith
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let t := Real.sqrt x / (4 * Real.sqrt A)
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) (by positivity)
  let n : ℕ := ⌊t⌋₊
  have hn : (n : ℝ) ≤ t := Nat.floor_le ht
  have htn : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  have htEq : 16 * A * t ^ 2 = x := by
    dsimp [t]
    field_simp
    nlinarith [Real.sq_sqrt hA.le, Real.sq_sqrt hx]
  have hf : (Nat.factorial (2 * n) : ℝ) ≤ (2 * (n : ℝ)) ^ (2 * n) := by
    exact_mod_cast Nat.factorial_le_pow (2 * n)
  have hpow : (2 * (n : ℝ)) ^ (2 * n) ≤ (2 * t) ^ (2 * n) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have huPow : x ^ n * u ≤ C * (x / 4) ^ n := by
    calc
      _ ≤ C * A ^ n * (Nat.factorial (2 * n) : ℝ) := h n
      _ ≤ C * A ^ n * (2 * t) ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (hf.trans hpow) (by positivity)
      _ = C * (x / 4) ^ n := by
        rw [pow_mul, mul_assoc, ← mul_pow]
        congr 2
        nlinarith only [htEq]
  have huQuarter : u ≤ C * (1 / 4 : ℝ) ^ n := by
    have he : C * (x / 4) ^ n = x ^ n * (C * (1 / 4 : ℝ) ^ n) := by
      rw [show x / 4 = x * (1 / 4 : ℝ) by ring, mul_pow]
      ring
    rw [he] at huPow
    exact (mul_le_mul_iff_right₀ (pow_pos hxpos n)).mp huPow
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have heExp : (1 / 4 : ℝ) ^ n = Real.exp (-Real.log 4 * (n : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
    simp only [one_div]
  calc
    u ≤ C * (1 / 4 : ℝ) ^ n := huQuarter
    _ = C * Real.exp (-Real.log 4 * (n : ℝ)) := by rw [heExp]
    _ ≤ C * Real.exp (Real.log 4 - Real.log 4 * t) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith only [htn, hlog]
    _ = 4 * C * Real.exp (-(Real.log 4 / (4 * Real.sqrt A)) * Real.sqrt x) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
      rw [show -(Real.log 4 * t) = -(Real.log 4 / (4 * Real.sqrt A)) * Real.sqrt x by
        dsimp [t]
        ring]
      ring

end WaveTurbulence.Fourier
