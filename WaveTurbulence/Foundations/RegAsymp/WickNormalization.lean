/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.WickGain
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact normalization and codimension gain of source Wick slices -/

public section
namespace WaveTurbulence.RegAsymp

/-- One free lattice vector and one removed NT pair give the literal
power L^(-(d-2gamma)), retaining the source delta square. -/
theorem wick_one_link_normalization {d : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ) :
    (δ/(2*L^((d:ℝ)-γ)))^2*(2^d*L^d) =
      (2^d*δ^2/4)*L^(-((d:ℝ)-2*γ)) := by
  have hquot : L^d/(L^((d:ℝ)-γ))^2 = L^(-((d:ℝ)-2*γ)) := by
    rw [show (L^((d:ℝ)-γ))^2 = L^(((d:ℝ)-γ)*2) by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
      norm_num,
      ← Real.rpow_natCast,← Real.rpow_sub hL]
    congr 1
    ring
  rw [div_pow,mul_pow]
  calc
    _ = (2^d*δ^2/4)*(L^d/(L^((d:ℝ)-γ))^2) := by norm_num; ring
    _ = _ := by rw [hquot]

/-- Every nonempty Wick slice keeps the required gamma1 decay after
paying a quarter-power of L for each traced coefficient variable. -/
theorem wick_gain_after_trace {d r : ℕ} (hd : 3 ≤ d) {L γ : ℝ}
    (hL : 1 ≤ L) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hr : 1 ≤ r) :
    (L^(-((d:ℝ)-2*γ)))^r*L^((r:ℝ)/4) ≤ L^(-ApproxNT.gamma1 d γ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hg : 0 ≤ ApproxNT.gamma1 d γ := by
    unfold ApproxNT.gamma1
    have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
    exact le_min (by linarith [hγ.1]) (le_min (by norm_num)
      (mul_nonneg (by linarith) (by linarith [hγ.2])))
  have hm := wick_dimension_margin hd γ
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le,← Real.rpow_add hL0]
  apply Real.rpow_le_rpow_of_exponent_le hL
  nlinarith

end WaveTurbulence.RegAsymp
