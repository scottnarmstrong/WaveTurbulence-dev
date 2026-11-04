/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The axis-error power budget on a nonempty long-time window

TARGET (incohproof12)–(incohproof13). Nonemptiness supplies `L ≤ T L^(2γ)`;
this absorbs the axis error even when `γ < 1/2`. No eventual-nonemptiness
assumption or unnecessary restriction on `γ` is introduced.
-/

public section

namespace WaveTurbulence.Incoh

/-- The integrated axis correction fits the long-time exponent whenever that window is nonempty. -/
theorem axis_longTime_power_le {d : ℕ} (hd : 2 ≤ d) {L T γ : ℝ}
    (hL : 0 < L) (hT : 0 ≤ T) (hwindow : L ≤ T * L ^ (2 * γ)) :
    L ^ ((d : ℝ) + 2 * γ) ≤
      T ^ ((d : ℝ) - 2) * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ)) := by
  have hd' : 0 ≤ (d : ℝ) - 2 := sub_nonneg.mpr (by exact_mod_cast hd)
  have hp := Real.rpow_le_rpow hL.le hwindow hd'
  rw [Real.mul_rpow hT (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hL.le] at hp
  calc
    _ = L ^ ((d : ℝ) - 2) * L ^ (2 + 2 * γ) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring
    _ ≤ (T ^ ((d : ℝ) - 2) * L ^ ((2 * γ) * ((d : ℝ) - 2))) * L ^ (2 + 2 * γ) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hL]
      congr 1
      congr 1
      ring

end WaveTurbulence.Incoh
