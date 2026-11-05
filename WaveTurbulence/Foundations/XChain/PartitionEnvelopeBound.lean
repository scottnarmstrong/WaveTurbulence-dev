/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionBracketBound
public import WaveTurbulence.Foundations.XChain.TopLeafCardBound
/-! Uniform majorants for the finite partition constants in the actual error bounds. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem partition_envelope_le {B h H : ℕ} (hB : B ≤ H) (hh : h ≤ H)
    {C b S : ℝ} (hC : 1 ≤ C) (hb : 0 ≤ b) (hS : 0 ≤ S) :
    2 ^ B * C ^ B * (2 ^ h : ℝ) ^ b * S ^ h ≤
      (2 * C) ^ H * (2 ^ H : ℝ) ^ b * (max 1 S) ^ H := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have h1 : (2 : ℝ) ^ B * C ^ B ≤ (2 * C) ^ H := by
    rw [← mul_pow]
    exact pow_le_pow_right₀ (by nlinarith) hB
  have h2 : (2 ^ h : ℝ) ^ b ≤ (2 ^ H : ℝ) ^ b :=
    Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) hh) hb
  have h3 : S ^ h ≤ (max 1 S) ^ H :=
    (pow_le_pow_left₀ hS (le_max_right 1 S) h).trans
      (pow_le_pow_right₀ (le_max_left 1 S) hh)
  exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _)
    (pow_nonneg (mul_nonneg (by norm_num) hC0) _)) h3 (pow_nonneg hS _)
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hC0) _) (Real.rpow_nonneg (by positivity) _))

end WaveTurbulence.Induct
