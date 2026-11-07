/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBGoodNormalization
import Mathlib.Tactic

/-! # Absorbing the component window factor in the good-operation margin -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter

theorem appb_s33_window_coefficient_eventual (γ0 : ℝ) (hγ0 : 0 < γ0) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ (1+Real.log L)^m →
      ((2*(n+1)+2 : ℕ) : ℝ)*(Real.log L)^16*L^(-(31/48)*γ0) ≤ L^(-5*γ0/8) := by
  have hraw := appb_log_coefficient_eventual 6 1 (-(31/48)*γ0) (-5*γ0/8) (m+16)
    (by nlinarith only [hγ0])
  filter_upwards [hraw,eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro n hn
  have hlog := Real.log_nonneg hL
  have hbase : 1 ≤ 1+Real.log L := by linarith only [hlog]
  have hp : (1 : ℝ) ≤ (1+Real.log L)^m := one_le_pow₀ hbase
  have hc : ((2*(n+1)+2 : ℕ) : ℝ) ≤ 6*(1+Real.log L)^m := by
    push_cast
    nlinarith only [hn,hp]
  have hpow : (Real.log L)^16 ≤ (1+Real.log L)^16 :=
    pow_le_pow_left₀ hlog (by linarith only [hlog]) 16
  have hcoef : ((2*(n+1)+2 : ℕ) : ℝ)*(Real.log L)^16 ≤ 6*(1+Real.log L)^(m+16) := by
    calc
      _ ≤ (6*(1+Real.log L)^m)*(1+Real.log L)^16 :=
        mul_le_mul hc hpow (pow_nonneg hlog _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  exact (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (zero_le_one.trans hL) _)).trans
    (by simpa only [inv_one,mul_one] using hb)

end WaveTurbulence.Mole
