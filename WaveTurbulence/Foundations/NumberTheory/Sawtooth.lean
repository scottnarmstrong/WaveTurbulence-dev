/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The right-continuous sawtooth

The convention in NT-CIRCLE-v2, goal 1, is `ψ(x) = x - floor x - 1/2`.
In particular its value at every integer is `-1/2`, rather than the midpoint
value zero. Fourier truncation estimates must retain an error at these points.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The sawtooth `x - floor x - 1/2`, including the value `-1/2` at integers. -/
@[expose] noncomputable def sawtooth (x : ℝ) : ℝ := Int.fract x - 1 / 2

theorem sawtooth_eq (x : ℝ) : sawtooth x = x - (⌊x⌋ : ℝ) - 1 / 2 := rfl

theorem neg_half_le_sawtooth (x : ℝ) : -(1 / 2 : ℝ) ≤ sawtooth x := by
  have h := Int.fract_nonneg x
  dsimp [sawtooth]
  linarith only [h]

theorem sawtooth_lt_half (x : ℝ) : sawtooth x < (1 / 2 : ℝ) := by
  have h := Int.fract_lt_one x
  dsimp [sawtooth]
  linarith only [h]

theorem abs_sawtooth_le_half (x : ℝ) : |sawtooth x| ≤ (1 / 2 : ℝ) :=
  abs_le.mpr ⟨neg_half_le_sawtooth x, (sawtooth_lt_half x).le⟩

@[simp] theorem sawtooth_intCast (n : ℤ) : sawtooth n = -(1 / 2 : ℝ) := by
  simp only [sawtooth, Int.fract_intCast, zero_sub]

@[simp] theorem sawtooth_add_intCast (x : ℝ) (n : ℤ) :
    sawtooth (x + n) = sawtooth x := by
  simp only [sawtooth, Int.fract_add_intCast]

theorem sawtooth_periodic : Function.Periodic sawtooth 1 := by
  intro x
  simpa only [Int.cast_one] using sawtooth_add_intCast x 1

theorem sawtooth_neg {x : ℝ} (hx : Int.fract x ≠ 0) :
    sawtooth (-x) = -sawtooth x := by
  simp only [sawtooth, Int.fract_neg hx]
  ring

end WaveTurbulence.NumberTheory
