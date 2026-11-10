/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadder
public import WaveTurbulence.Foundations.FinalCount.Degen.NormalizationFactors
import Mathlib.Tactic

/-! # Monotonic circuit-rank normalization and exact multiplicative ratios -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Degen

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
