/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.StageOrderLower
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! Fixed-order source estimates apply eventually as the torus size tends to infinity. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Filter

theorem eventually_order_le_stage (P : WTParams) (hd : 1 ≤ P.d) (q n : ℕ) :
    ∀ᶠ L : ℝ in atTop, n ≤ ({ P with L := L } : WTParams).N q ^ 4 := by
  have hh : ∀ᶠ L : ℝ in atTop, (n : ℝ) + 2 ≤ Real.log L :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hh] with L hL
  have hlog : 1 ≤ Real.log L := by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hN := log_sq_sub_one_le_N ({ P with L := L } : WTParams) hd hlog q
  have hs : (n : ℝ) ≤ Real.log L ^ 2 - 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (Real.log L - ((n : ℝ) + 2))]
  have hn : n ≤ ({ P with L := L } : WTParams).N q := by exact_mod_cast hs.trans hN
  by_cases hz : ({ P with L := L } : WTParams).N q = 0
  · simp_all
  · exact hn.trans (le_self_pow₀ (by omega) (by decide : (4 : ℕ) ≠ 0))

end WaveTurbulence.LGSpine
