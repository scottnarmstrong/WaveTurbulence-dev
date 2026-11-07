/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Scales
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The (Y2) constant is a power of `log L`, hence below any power of `L` -/

@[expose] public section
set_option autoImplicit false
open Finset Filter
namespace WaveTurbulence.MoleProp4

theorem card_scaleSet_le_log {L : ℝ} (hlog : 1 ≤ Real.log L) : ((scaleSet L).card : ℝ) ≤ 5 * Real.log L := by
  have h1 := card_scaleSet_le L
  have h2 : (⌊Real.logb 2 L⌋₊ : ℝ) ≤ Real.logb 2 L := Nat.floor_le (by
    rw [Real.logb]; exact div_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
  have h3 : Real.logb 2 L ≤ 2 * Real.log L := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  have h4 : ((scaleSet L).card : ℝ) ≤ ⌊Real.logb 2 L⌋₊ + 3 := by exact_mod_cast h1
  linarith

/-- **The (Y2) constant is eventually below `L ^ θ`.** -/
theorem eventually_ylem2Const_le {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, ∀ L ≥ R, 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 ≤ L ^ θ := by
  have hε : (0 : ℝ) < θ / 28 := by positivity
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp ((isLittleO_log_rpow_atTop hε).bound zero_lt_one)
  obtain ⟨R2, hR2⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < θ / 2)).eventually_ge_atTop
    (2750 : ℝ))
  refine ⟨max (max R1 R2) (Real.exp 1), fun L hL => ?_⟩
  have hL1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlogL : Real.log L ≤ L ^ (θ / 28) := by
    have : ‖Real.log L‖ ≤ 1 * ‖L ^ (θ / 28)‖ := hR1 L hL1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (by linarith),
      abs_of_nonneg (Real.rpow_nonneg hLp.le _)] at this
    exact this
  have hS := card_scaleSet_le_log hlog
  have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
  have hlog0 : (0 : ℝ) ≤ Real.log L := by linarith
  calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6
      ≤ 110 * (5 * Real.log L) ^ 2 * (Real.log L ^ 2) ^ 6 := by gcongr
    _ = 2750 * Real.log L ^ 14 := by ring
    _ ≤ 2750 * (L ^ (θ / 28)) ^ 14 := by gcongr
    _ = 2750 * L ^ (θ / 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]; norm_num; ring_nf
    _ ≤ L ^ (θ / 2) * L ^ (θ / 2) := by gcongr; exact hR2 L hL2
    _ = L ^ θ := by rw [← Real.rpow_add hLp]; ring_nf

end WaveTurbulence.MoleProp4
