/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.SourceNormalization
import Mathlib.Tactic

/-! # Monotonic circuit-rank normalization and exact multiplicative ratios -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Degen

/-- Circuit-rank normalization is a positive base raised to the actual
integer circuit rank. -/
theorem circuit_normalization_eq_zpow {L a B : ℝ} (hL : 0 ≤ L) (χ : ℤ) :
    L ^ (-a * (χ : ℝ)) * B ^ χ = (L ^ (-a) * B) ^ χ := by
  rw [Real.rpow_mul_intCast hL, mul_zpow]

/-- Losing circuits makes this normalization larger, for the source
standing range L≥1, d≥γ and 0<B≤1. -/
theorem circuit_normalization_antitone {L a B : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hB : 0 < B) (hB1 : B ≤ 1) {χpre χpost : ℤ} (hχ : χpost ≤ χpre) :
    L ^ (-a * (χpre : ℝ)) * B ^ χpre ≤ L ^ (-a * (χpost : ℝ)) * B ^ χpost := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : L ^ (-a) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [ha] : -a ≤ 0)
    simpa only [Real.rpow_zero] using hh
  have hb : L ^ (-a) * B ≤ 1 := by
    have hh := mul_le_mul hp hB1 hB.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  rw [circuit_normalization_eq_zpow hL0.le, circuit_normalization_eq_zpow hL0.le]
  exact zpow_le_zpow_right_of_le_one₀ (mul_pos (Real.rpow_pos_of_pos hL0 _) hB) hb hχ

/-- The exact scalar normalization ratio separates circuit and ladder factors. -/
theorem circuit_normalization_ratio {L a B Wpre Wpost : ℝ} (hL : 0 < L) (hB : B ≠ 0)
    (hW : Wpost ≠ 0) (χpre χpost : ℤ) :
    (L ^ (-a * (χpre : ℝ)) * B ^ χpre * Wpre) /
      (L ^ (-a * (χpost : ℝ)) * B ^ χpost * Wpost) =
    L ^ (-a * ((χpre - χpost : ℤ) : ℝ)) * B ^ (χpre - χpost) * (Wpre / Wpost) := by
  rw [Int.cast_sub, mul_sub, neg_mul, neg_mul]
  rw [Real.rpow_sub hL, zpow_sub₀ hB]
  ring

end WaveTurbulence.Degen
