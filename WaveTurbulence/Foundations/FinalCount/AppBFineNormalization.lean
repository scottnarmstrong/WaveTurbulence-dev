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

/-- Conditional scalar arithmetic helper. The raw count premise is kept
separate from every source-facing operation theorem. No division by the
post count is used, including when it is zero. -/
theorem appb_fine_normalization_of_raw (Epre Epos : ℝ≥0∞) (χ : ℤ) (L D B H η : ℝ)
    (hL : 1 ≤ L) (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η)
    (hraw : Epre ≤ ENNReal.ofReal (L^(D-3*η/4))*Epos) :
    Epre*ENNReal.ofReal (L^(-D*((χ+1 : ℤ) : ℝ))*B^(χ+1)*H) ≤
      ENNReal.ofReal (L^(-η/2))*(Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*H)) := by
  have hLp := zero_lt_one.trans_le hL
  have hfac : 0 ≤ L^(-D)*B := by positivity
  have hpow : 0 ≤ L^(D-3*η/4) := Real.rpow_nonneg hLp.le _
  have hcoef : L^(D-3*η/4)*(L^(-D)*B) ≤ L^(-η/2) := by
    calc
      _ = L^(-3*η/4)*B := by
        rw [← mul_assoc,← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ L^(-3*η/4) := mul_le_of_le_one_right (by positivity) hB1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hη])
  rw [appb_normalization_step_one χ L D B H hLp hB.ne',ENNReal.ofReal_mul hfac]
  calc
    _ = (Epre*ENNReal.ofReal (L^(-D)*B))*ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*H) := by ring
    _ ≤ ((ENNReal.ofReal (L^(D-3*η/4))*Epos)*ENNReal.ofReal (L^(-D)*B))*
        ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*H) :=
      mul_le_mul_left (mul_le_mul_left hraw _) _
    _ = ENNReal.ofReal (L^(D-3*η/4)*(L^(-D)*B))*
        (Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*H)) := by
      rw [ENNReal.ofReal_mul hpow]
      ring
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoef) _

end WaveTurbulence.Mole
