/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! # Each Wick codimension pays its own factorial trace cost

For n≤(log L)^A and r≤n, the trace cost C^r(2r)! is at most L^(εr)
for all sufficiently large L. This permits arbitrary fixed polylogarithmic
order exponents without incorrectly bounding n! by L^ε.
-/

public section
namespace WaveTurbulence.RegAsymp
open Filter

/-- A uniform quadratic polylogarithmic bound, before raising to codimension. -/
theorem exists_polylog_quadratic_threshold {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 1 ≤ L ∧
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^A → C*(2*(n:ℝ))^2 ≤ L^ε := by
  have hp : ∀ᶠ L : ℝ in atTop, Real.log L^A ≤ L^(ε/4) := by
    have h := (isLittleO_log_rpow_rpow_atTop A (by positivity : 0 < ε/4)).bound (by norm_num : (0:ℝ)<1)
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L hL hL1
    rw [one_mul,Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) _)] at hL
    exact hL
  have hc : ∀ᶠ L : ℝ in atTop, 4*C ≤ L^(ε/2) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε/2)).eventually_ge_atTop _
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (1:ℝ)).and (hp.and hc))
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨hL1,hpoly,hconst⟩ := hL₀ L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨hL1,?_⟩
  intro n hn
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg n) (hn.trans hpoly) 2
  calc
    _ = (4*C)*(n:ℝ)^2 := by ring
    _ ≤ (4*C)*(L^(ε/4))^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (4*C)*L^(ε/2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      congr 2
      ring
    _ ≤ L^(ε/2)*L^(ε/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = L^ε := by rw [← Real.rpow_add hL0]; congr 1; ring

/-- Every fixed polynomial in a polylogarithmic order is eventually a small power of L. -/
theorem exists_polylog_power_threshold {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (p : ℕ) (hp : 0 < p) (A : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 1 ≤ L ∧
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^A → C*(2*(n:ℝ))^p ≤ L^ε := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  let s := ε/(2*(p:ℝ))
  have hs : 0 < s := by dsimp only [s]; positivity
  have hpoly : ∀ᶠ L : ℝ in atTop, Real.log L^A ≤ L^s := by
    have h := (isLittleO_log_rpow_rpow_atTop A hs).bound (by norm_num : (0:ℝ)<1)
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L hL hL1
    rw [one_mul,Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) _)] at hL
    exact hL
  have hconst : ∀ᶠ L : ℝ in atTop, C*2^p ≤ L^(ε/2) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε/2)).eventually_ge_atTop _
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (1:ℝ)).and (hpoly.and hconst))
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨hL1,hP,hC'⟩ := hL₀ L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨hL1,?_⟩
  intro n hn
  have hnp := pow_le_pow_left₀ (Nat.cast_nonneg n) (hn.trans hP) p
  calc
    _ = (C*2^p)*(n:ℝ)^p := by rw [mul_pow]; ring
    _ ≤ (C*2^p)*(L^s)^p := mul_le_mul_of_nonneg_left hnp (by positivity)
    _ = (C*2^p)*L^(ε/2) := by
      rw [← Real.rpow_natCast (L^s),← Real.rpow_mul hL0.le]
      congr 2
      dsimp only [s]
      field_simp
    _ ≤ L^(ε/2)*L^(ε/2) := mul_le_mul_of_nonneg_right hC' (by positivity)
    _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring

/-- The factorial cost is absorbed per traced link, uniformly over the
entire allowed order range and every codimension r≤n. -/
theorem exists_wick_trace_factorial_threshold {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 1 ≤ L ∧
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^A → ∀ r : ℕ, r ≤ n →
        C^r*((2*r).factorial:ℝ) ≤ L^(ε*(r:ℝ)) := by
  obtain ⟨L₀,hL₀⟩ := exists_polylog_quadratic_threshold hC hε A
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨hL1,hbase⟩ := hL₀ L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨hL1,?_⟩
  intro n hn r hr
  have hfac : ((2*r).factorial:ℝ) ≤ (2*(n:ℝ))^(2*r) := by
    have hf : ((2*r).factorial:ℝ) ≤ ((2*r:ℕ):ℝ)^(2*r) := by
      exact_mod_cast Nat.factorial_le_pow (2*r)
    apply hf.trans
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 hr
  calc
    _ ≤ C^r*(2*(n:ℝ))^(2*r) := mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (C*(2*(n:ℝ))^2)^r := by rw [pow_mul,← mul_pow]
    _ ≤ (L^ε)^r := pow_le_pow_left₀ (by positivity) (hbase n hn) r
    _ = L^(ε*(r:ℝ)) := by rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]

/-- The full cube-inequality trace cost, including r^r, is absorbed per codimension. -/
theorem exists_wick_block_trace_threshold {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (A : ℝ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 1 ≤ L ∧
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^A → ∀ r : ℕ, r ≤ n →
        C^r*(r:ℝ)^r*((2*r).factorial:ℝ) ≤ L^(ε*(r:ℝ)) := by
  obtain ⟨L₀,hL₀⟩ := exists_polylog_power_threshold hC hε 3 (by decide) A
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨hL1,hbase⟩ := hL₀ L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨hL1,?_⟩
  intro n hn r hr
  have hfac : ((2*r).factorial:ℝ) ≤ (2*(n:ℝ))^(2*r) := by
    have hf : ((2*r).factorial:ℝ) ≤ ((2*r:ℕ):ℝ)^(2*r) := by exact_mod_cast Nat.factorial_le_pow (2*r)
    apply hf.trans
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 hr
  have hr' : (r:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast hr.trans (Nat.le_mul_of_pos_left n (by decide : 0<2))
  calc
    _ ≤ C^r*(2*(n:ℝ))^r*(2*(n:ℝ))^(2*r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg r) hr' r) (by positivity)) hfac
        (by positivity) (by positivity)
    _ = (C*(2*(n:ℝ))^3)^r := by
      rw [pow_mul,← mul_pow,← mul_pow]
      congr 1
      ring
    _ ≤ (L^ε)^r := pow_le_pow_left₀ (by positivity) (hbase n hn) r
    _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]

end WaveTurbulence.RegAsymp
