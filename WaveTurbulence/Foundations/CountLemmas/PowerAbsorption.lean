/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Eventual absorption of fixed constants and logarithms into strict power gains -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

/-- A strict power gap absorbs any fixed constant and fixed logarithmic
power. The threshold may depend on that constant, as in COUNT's δ-dependent
large-L convention. -/
theorem eventually_monomial_log_le {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, C*L^a*(1+Real.log L)^m ≤ L^b := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (m : ℝ) (sub_pos.mpr hab)).const_mul_left (C*2^m)
  have hb := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1 : ℝ)] with L hbound hlog hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlog0 : 0 ≤ Real.log L := zero_le_one.trans hlog
  have hh : (C*2^m)*(Real.log L)^m ≤ L^(b-a) := by
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (by positivity : 0 ≤ (C*2^m)*(Real.log L)^m),
      Real.norm_of_nonneg (Real.rpow_nonneg hLp.le (b-a)),one_mul] using hbound
  have hpow : (1+Real.log L)^m ≤ 2^m*(Real.log L)^m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hlog]) m
  calc
    _ ≤ C*L^a*(2^m*(Real.log L)^m) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = L^a*((C*2^m)*(Real.log L)^m) := by ring
    _ ≤ L^a*L^(b-a) := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hLp.le _)
    _ = L^b := by rw [← Real.rpow_add hLp]; congr 1; ring

/-- The same strict gap leaves an inverse squared logarithm in the final
bound, with no constant depending on δ outside its threshold. -/
theorem eventually_monomial_log_le_div_log_sq {a b C : ℝ} (hab : a < b)
    (hC : 0 ≤ C) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, C*L^a*(1+Real.log L)^m ≤ L^b/(Real.log L)^2 := by
  have hb := eventually_monomial_log_le hab hC (m+2)
  filter_upwards [hb,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1 : ℝ)] with L hbound hlog hL
  have hlp : 0 < Real.log L := lt_of_lt_of_le zero_lt_one hlog
  apply (le_div_iff₀ (sq_pos_of_pos hlp)).mpr
  calc
    _ ≤ C*L^a*(1+Real.log L)^m*(1+Real.log L)^2 := mul_le_mul_of_nonneg_left
      (by nlinarith only [hlog,sq_nonneg (Real.log L)] : (Real.log L)^2 ≤ (1+Real.log L)^2) (by positivity)
    _ = C*L^a*(1+Real.log L)^(m+2) := by rw [pow_add]; ring
    _ ≤ L^b := hbound

end WaveTurbulence.CountLemmas
