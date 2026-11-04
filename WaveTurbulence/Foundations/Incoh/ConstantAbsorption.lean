/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Absorbing secondary constants at a large-box threshold

TARGET (incohproof16), (incohproof18): the base constant stays independent
of the layer range and coupling. Secondary constants enter only the threshold.
-/

public section

namespace WaveTurbulence.Incoh

/-- A secondary constant is bounded by any positive power at a threshold independent of link count. -/
theorem exists_constant_absorption_threshold (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, C ≤ L ^ ε := by
  obtain ⟨L₀, hb⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop hε).eventually_ge_atTop C)
  exact ⟨max L₀ 1, le_max_right _ _, fun L hL => hb L ((le_max_left _ _).trans hL)⟩

/-- A decaying long-frequency term can be made smaller than one fixed base constant. -/
theorem exists_decaying_constant_threshold {C : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, C * L ^ (-ε) ≤ 1 := by
  obtain ⟨L₀, hL₀, hb⟩ := exists_constant_absorption_threshold C hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₀.trans hL)
  calc
    _ ≤ L ^ ε * L ^ (-ε) := mul_le_mul_of_nonneg_right (hb L hL) (Real.rpow_nonneg hLp.le _)
    _ = 1 := by rw [← Real.rpow_add hLp, add_neg_cancel, Real.rpow_zero]

/-- The same threshold absorbs `C^g` for every finite incoherence count simultaneously. -/
theorem exists_counted_constant_absorption_threshold {C : ℝ} (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ g : ℕ, C ^ g ≤ L ^ (ε * g) := by
  obtain ⟨L₀, hL₀, hb⟩ := exists_constant_absorption_threshold C hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL g
  have hLp : 0 < L := zero_lt_one.trans_le (hL₀.trans hL)
  calc
    _ ≤ (L ^ ε) ^ g := pow_le_pow_left₀ hC (hb L hL) g
    _ = _ := by rw [← Real.rpow_natCast (L ^ ε) g, ← Real.rpow_mul hLp.le]

end WaveTurbulence.Incoh
