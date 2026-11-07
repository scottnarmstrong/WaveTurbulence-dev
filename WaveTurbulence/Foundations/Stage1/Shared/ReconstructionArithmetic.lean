/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Factorial/exponential bounds for reconstruction records

DH21-2 Proposition 6.4: root records may range over all atom slots.
The factor n^r is absorbed by r! times an exponential in n; no restriction
to a smaller, unproved root-record carrier is used.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- An ordered list of r choices among n possibilities costs at most r!
times 3^n. This absorbs the apparent polynomial dependence on atom count. -/
theorem pow_le_factorial_mul_three_pow (n r : ℕ) : n^r ≤ r.factorial*3^n := by
  have h := Real.pow_div_factorial_le_exp (n:ℝ) (Nat.cast_nonneg n) r
  have he : Real.exp (n : ℝ) ≤ (3:ℝ)^n := by
    rw [← mul_one (n:ℝ),Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  have hfac : 0 < (r.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hh := (div_le_iff₀ hfac).mp (h.trans he)
  exact_mod_cast hh.trans_eq (mul_comm _ _)

/-- The actual root record and signature choices, for fixed atom count n
and width w, fit a factorial in w times an exponential in n+w. -/
theorem root_records_bound (n w : ℕ) :
    (4*n+w)^w*2^w ≤ w.factorial*3^(4*n+2*w) := by
  calc
    (4*n+w)^w*2^w ≤ (w.factorial*3^(4*n+w))*3^w :=
      Nat.mul_le_mul (pow_le_factorial_mul_three_pow _ _) (Nat.pow_le_pow_left (by omega) _)
    _ = w.factorial*3^(4*n+2*w) := by rw [mul_assoc,← pow_add]; congr 2; omega

/-- The width-dependent exponential is absorbed by a factorial in width. -/
theorem factorial_mul_nine_pow_le (w : ℕ) : w.factorial*9^w ≤ (9*w).factorial := by
  by_cases hw : w < 8
  · interval_cases w <;> norm_num
  · have hbase : 9 ≤ w+1 := by omega
    calc
      w.factorial*9^w ≤ w.factorial*(w+1)^w :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase w)
      _ ≤ (w+w).factorial := Nat.factorial_mul_pow_le_factorial
      _ ≤ (9*w).factorial := Nat.factorial_le (by omega)

/-- An explicit universal reconstruction constant. -/
theorem reconstruction_arithmetic (n w : ℕ) :
    256^n*(4*n+w)^w*2^w ≤ (9*w).factorial*20736^n := by
  calc
    _ = 256^n*((4*n+w)^w*2^w) := Nat.mul_assoc _ _ _
    _ ≤ 256^n*(w.factorial*3^(4*n+2*w)) := Nat.mul_le_mul_left _ (root_records_bound n w)
    _ = (w.factorial*9^w)*20736^n := by
      rw [pow_add,pow_mul,pow_mul]
      norm_num
      rw [show (20736:ℕ) = 256*81 by decide,mul_pow]
      ring
    _ ≤ (9*w).factorial*20736^n := Nat.mul_le_mul_right _ (factorial_mul_nine_pow_le w)

end WaveTurbulence.Mole
