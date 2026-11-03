/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The short-window condition from the source parameters

TARGET `lemlin` uses `δ ≤ 1` and `γ + η ≤ 1`, consequences of its standing
smallness assumptions. These suffice for the explicit one-period condition.
-/

public section

namespace WaveTurbulence.LemLin

/-- The upper source bound on the momentum makes the time window short. -/
theorem source_window_short {d : ℕ} {L δ γ η : ℝ} (hL : 1 ≤ L)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hγη : γ + η ≤ 1)
    (r : Mom d) (hr : ‖r‖ ≤ L ^ (-γ + η)) :
    (δ * L ^ (2 * γ)) * ‖r‖ ≤ L := by
  have hLpos : 0 < L := by linarith
  calc
    _ ≤ (δ * L ^ (2 * γ)) * L ^ (-γ + η) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hδ0 (Real.rpow_nonneg hLpos.le _))
    _ = δ * L ^ (γ + η) := by
      rw [mul_assoc, ← Real.rpow_add hLpos]
      congr 2
      ring
    _ ≤ L ^ (γ + η) := mul_le_of_le_one_left (Real.rpow_nonneg hLpos.le _) hδ1
    _ ≤ L := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL hγη

end WaveTurbulence.LemLin
