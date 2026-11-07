/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Absorbing later constants into strict exponent reserves

The exact sumint prefix chooses C₁ before δ and Dsteps, but permits L₀
to depend on them. A fixed positive exponent reserve absorbs any such
constant, and the same threshold works for every number of bad factors.
-/

@[expose] public section
set_option autoImplicit false

open Filter

namespace WaveTurbulence.SumintPar

/-- Every fixed real constant is bounded by a positive power beyond a threshold at least two. -/
theorem exists_constant_le_rpow (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L ≥ L₀, K ≤ L^ε := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (eventually_ge_atTop K))
  exact ⟨max R 2,le_max_right _ _,fun L hL => hR L ((le_max_left _ _).trans hL)⟩

/-- A constant multiplying a logarithm is also absorbed by any positive reserve. -/
theorem exists_constant_log_le_rpow (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L ≥ L₀, K*Real.log L ≤ L^ε := by
  have he : ∀ᶠ L : ℝ in atTop, K*Real.log L ≤ L^ε := by
    have hb := ((isLittleO_log_rpow_atTop hε).const_mul_left K).bound
      (by norm_num : (0:ℝ) < 1)
    filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with L hL hLp
    have hh : |K*Real.log L| ≤ |L^ε| := by simpa only [Real.norm_eq_abs,one_mul] using hL
    rw [abs_of_nonneg (Real.rpow_nonneg hLp ε)] at hh
    exact (le_abs_self _).trans hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  exact ⟨max R 2,le_max_right _ _,fun L hL => hR L ((le_max_left _ _).trans hL)⟩

/-- A single power reserve absorbs the same constant simultaneously in any number of factors. -/
theorem pow_constant_rpow_le {L K ε a : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (hbound : K ≤ L^ε) (N : ℕ) :
    (K*L^a)^N ≤ L^((a+ε)*(N:ℝ)) := by
  have hsingle : K*L^a ≤ L^(a+ε) := by
    calc
      _ ≤ L^ε*L^a := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  calc
    _ ≤ (L^(a+ε))^N := pow_le_pow_left₀ (mul_nonneg hK (Real.rpow_nonneg hL.le _)) hsingle N
    _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]

end WaveTurbulence.SumintPar
