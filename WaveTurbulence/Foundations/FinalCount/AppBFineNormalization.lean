/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCounting
import Mathlib.Tactic

/-! # Scalar normalization for a circuit-rank-one fine removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal

theorem appb_normalization_step_one (χ : ℤ) (L D B H : ℝ) (hL : 0 < L) (hB : B ≠ 0) :
    L^(-D*((χ+1 : ℤ) : ℝ))*B^(χ+1)*H =
      (L^(-D)*B)*(L^(-D*(χ : ℝ))*B^χ*H) := by
  have he : -D*((χ+1 : ℤ) : ℝ) = -D*(χ : ℝ)+(-D) := by push_cast; ring
  rw [he,Real.rpow_add hL,zpow_add₀ hB,zpow_one]
  ring

end WaveTurbulence.Mole
