/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Uniform logarithm absorption for actual K4 coefficient blocks

The translated harmonic factor is uniform over every radius R≤1. Its
power majorant has a constant depending only on the chosen exponent.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- The actual harmonic factor is positive throughout the used radius range. -/
theorem k4_harmonic_factor_one_le {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) :
    1 ≤ 3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ) := by
  have hbase : (1 : ℝ) ≤ 2*(L*R)+1 := by nlinarith only [mul_nonneg hL hR]
  have hN : (1 : ℝ) ≤ (⌈2*(L*R)+1⌉₊ : ℝ) := hbase.trans (Nat.le_ceil _)
  have hh := Real.log_nonneg hN
  linarith only [hh]

/-- A constant uniform over all source coefficient blocks absorbs the
literal translated harmonic factor into any prescribed positive power. -/
theorem k4_harmonic_factor_le_rpow {L R ε : ℝ} (hL : 1 ≤ L)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hε : 0 < ε) :
    3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ) ≤
      (3+2*(4 : ℝ)^ε/ε)*L^ε := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hN0 : (0 : ℝ) ≤ (⌈2*(L*R)+1⌉₊ : ℝ) := Nat.cast_nonneg _
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*(L*R)+1)
  have hLR : L*R ≤ L := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR1 hLp.le
  have hN4 : (⌈2*(L*R)+1⌉₊ : ℝ) ≤ 4*L := by linarith only [hceil,hLR,hL]
  have hlog := Real.log_le_rpow_div hN0 hε
  have hp := Real.rpow_le_rpow hN0 hN4 hε.le
  have hdiv := div_le_div_of_nonneg_right hp hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤4) hLp.le] at hdiv
  have hP1 : 1 ≤ L^ε := Real.one_le_rpow hL hε.le
  have hm := mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ)≤3)
  have he : (3+2*(4 : ℝ)^ε/ε)*L^ε = 3*L^ε+2*((4 : ℝ)^ε*L^ε/ε) := by ring
  rw [he]
  linarith only [hlog,hdiv,hm]

end WaveTurbulence.MoleProp
