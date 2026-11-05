/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final4a
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
/-! Eventual inequalities on `L` and the parameter choices. -/
@[expose] public section
open Filter Topology
namespace WaveTurbulence.Ladder

theorem eventually_log_pow_le (k : ℕ) (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, c * (Real.log L) ^ k ≤ L ^ ε := by
  have h := isLittleO_log_rpow_rpow_atTop (k : ℝ) hε
  have hpos : (0 : ℝ) < 1 / (c + 1) := by positivity
  have := h.bound hpos
  filter_upwards [this, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.rpow_natCast] at hL
  have h2 : (c + 1) * (Real.log L) ^ k ≤ L ^ ε := by
    have := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ c + 1 by linarith)
    calc (c + 1) * (Real.log L) ^ k ≤ (c + 1) * (1 / (c + 1) * L ^ ε) := this
      _ = L ^ ε := by field_simp
  have : c * (Real.log L) ^ k ≤ (c + 1) * (Real.log L) ^ k := by
    gcongr; linarith
  linarith

theorem arsinh_le_log (x : ℝ) (hx : 0 ≤ x) : Real.arsinh x ≤ Real.log (2 * x + 1) := by
  unfold Real.arsinh
  apply Real.log_le_log (by positivity)
  have : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith
  linarith

theorem Y_bound {L : ℝ} {d : ℕ} (hL1 : 1 ≤ L) (hΛ : 20 ≤ Real.log L) (hd : 1 ≤ d) :
    3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM0 : 0 ≤ Mv d L := by unfold Mv; positivity
  have hfl : ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
    have := Nat.floor_le (show 0 ≤ 2 * L by linarith)
    push_cast; linarith
  have hMv : Mv d L ≤ 2 * (3 * L) ^ (4 * d) := by
    unfold Mv
    gcongr
  have h2M : 2 * Mv d L + 1 ≤ (3 * L) ^ (4 * d + 2) := by
    have h1 : (1 : ℝ) ≤ (3 * L) ^ (4 * d) := one_le_pow₀ (by linarith)
    have h3 : (3 * L) ^ (4 * d + 2) = (3 * L) ^ (4 * d) * (3 * L) ^ 2 := pow_add _ _ _
    have h4 : (9 : ℝ) ≤ (3 * L) ^ 2 := by nlinarith
    nlinarith
  have hlog3 : Real.log (3 * L) ≤ 1.1 * Real.log L := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hars : Real.arsinh (Mv d L) ≤ (4 * d + 2) * (1.1 * Real.log L) := by
    refine (arsinh_le_log _ hM0).trans ?_
    refine (Real.log_le_log (by positivity) h2M).trans ?_
    rw [Real.log_pow]
    push_cast
    exact mul_le_mul_of_nonneg_left hlog3 (by positivity)
  nlinarith

end WaveTurbulence.Ladder
