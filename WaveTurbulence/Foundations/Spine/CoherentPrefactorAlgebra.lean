/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! Separate the fixed high-order coherent cost from the low-order exponential base. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem coherent_error_prefactor_identity (M C δ D U a : ℝ) (n k : ℕ) :
    M ^ n * ((C * (C * δ) ^ n * a) * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))) =
      (D * C ^ 2 * U ^ k) * (8 * M * C ^ 3 * δ) ^ n * a := by
  have hc : C ^ 3 = C * C ^ 2 := by ring
  simp only [hc, mul_pow, pow_add, pow_mul, pow_one]
  ring

 theorem coherent_remainder_prefactor_identity (M C δ D U ε : ℝ) (n k : ℕ) :
    M ^ n * ((2 : ℝ) ^ (2 * n + 1) *
      (((2 : ℝ) ^ n * δ ^ n * (C * C ^ n) ^ 2) *
        (ε * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))))) =
      (2 * D * C ^ 3 * U ^ k) * (64 * M * C ^ 4 * δ) ^ n * ε := by
  have h64 : (64 : ℝ) = 2 ^ 2 * 2 * 8 := by norm_num
  have hc : C ^ 4 = C ^ 2 * C ^ 2 := by ring
  rw [h64, hc]
  simp only [mul_pow, pow_add, pow_mul, pow_one, pow_right_comm C n 2]
  ring

/-- Only M and the low norm C enter the order-dependent base. The high norm U is
raised to k, fixed by the requested seminorm, and remains an outside cost. -/
theorem coherent_prefactor_le_common_base {M C δ D U a ε : ℝ} (n k : ℕ)
    (hM : 0 ≤ M) (hC : 1 ≤ C) (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    M ^ n * (((C * (C * δ) ^ n * a) * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k))) +
      ((2 : ℝ) ^ (2 * n + 1) * (((2 : ℝ) ^ n * δ ^ n * (C * C ^ n) ^ 2) *
        (ε * (D * 8 ^ n * (C ^ (2 * n + 1) * U ^ k)))))) ≤
      (2 * D * C ^ 3 * U ^ k) * (64 * M * C ^ 4 * δ) ^ n * (a + ε) := by
  rw [mul_add, coherent_error_prefactor_identity, coherent_remainder_prefactor_identity]
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hcoef : D * C ^ 2 * U ^ k ≤ 2 * D * C ^ 3 * U ^ k := by
    have hh : C ^ 2 ≤ 2 * C ^ 3 := by nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC)]
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hD) (pow_nonneg hU k)
    convert ht using 1 <;> ring
  have hbase : 8 * M * C ^ 3 * δ ≤ 64 * M * C ^ 4 * δ := by
    have hh : 8 * C ^ 3 ≤ 64 * C ^ 4 := by
      have hpow : C ^ 3 ≤ C ^ 4 := pow_le_pow_right₀ hC (by decide)
      nlinarith [pow_nonneg hC0 3]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hM) hδ]
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul hcoef (pow_le_pow_left₀ (by positivity) hbase n) (by positivity) (by positivity)) ha
  calc
    _ ≤ (2 * D * C ^ 3 * U ^ k) * (64 * M * C ^ 4 * δ) ^ n * a +
        (2 * D * C ^ 3 * U ^ k) * (64 * M * C ^ 4 * δ) ^ n * ε := add_le_add hterm le_rfl
    _ = _ := by ring

end WaveTurbulence.LGSpine
