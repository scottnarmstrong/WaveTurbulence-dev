/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Monomial comparisons across derivative-test frequency ranges

Two elementary real-power comparisons express interpolation between a
frequency scale and a length scale. These are scalar identities and do
not assert an exponential-sum bound.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Compare two monomials using an upper frequency-to-length relation. -/
theorem rpow_mul_le_of_upper_scale {N T a b c d u : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hscale : T ≤ N^u) (hac : c ≤ a)
    (hexp : u*(a-c)+b ≤ d) : T^a*N^b ≤ T^c*N^d := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hf : T^(a-c) ≤ (N^u)^(a-c) :=
    Real.rpow_le_rpow hT.le hscale (sub_nonneg.mpr hac)
  calc
    _ = T^c*(T^(a-c)*N^b) := by rw [← mul_assoc,← Real.rpow_add hT]; congr 2; ring
    _ ≤ T^c*((N^u)^(a-c)*N^b) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hNp.le _)) (Real.rpow_nonneg hT.le _)
    _ = T^c*N^(u*(a-c)+b) := by rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexp)
      (Real.rpow_nonneg hT.le _)

/-- Compare two monomials using a lower frequency-to-length relation. -/
theorem rpow_mul_le_of_lower_scale {N T a b c d l : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hscale : N^l ≤ T) (hac : a ≤ c)
    (hexp : l*(a-c)+b ≤ d) : T^a*N^b ≤ T^c*N^d := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hf : T^(a-c) ≤ (N^l)^(a-c) := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hNp _) hscale (sub_nonpos.mpr hac)
  calc
    _ = T^c*(T^(a-c)*N^b) := by rw [← mul_assoc,← Real.rpow_add hT]; congr 2; ring
    _ ≤ T^c*((N^l)^(a-c)*N^b) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hNp.le _)) (Real.rpow_nonneg hT.le _)
    _ = T^c*N^(l*(a-c)+b) := by rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexp)
      (Real.rpow_nonneg hT.le _)

/-- Normalize a derivative-test term at scale `T/N^k`. -/
theorem rpow_mul_div_pow_identity {N T : ℝ} (hN : 0 < N) (hT : 0 < T)
    (u a : ℝ) (k : ℕ) :
    N^u*(T/N^k)^a = T^a*N^(u-(k:ℝ)*a) := by
  rw [Real.div_rpow hT.le (pow_nonneg hN.le k),← Real.rpow_natCast_mul hN.le,
    Real.rpow_sub hN]
  ring

end WaveTurbulence.NumberTheory
