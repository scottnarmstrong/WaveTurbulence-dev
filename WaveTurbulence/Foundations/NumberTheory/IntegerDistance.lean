/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license; see SALT-LICENSE in this directory.
Authors: Jason Hickey, Claude
Adapted for WaveTurbulence by Scott Armstrong.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Distance modulo the integers

Distance from `x-y` to its nearest integer, with the minimizing property,
triangle inequality, and translation invariance proved for every real input.
Adapted from Jason Hickey's `Salt/LS/Dist.lean`, commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The mod-1 circle distance: the distance from `x - y` to the nearest
integer. -/
@[expose] noncomputable def integerDistance (x y : ℝ) : ℝ := |x - y - round (x - y)|

/-- `integerDistance x x = 0`. -/
@[simp]
theorem integerDistance_self (x : ℝ) : integerDistance x x = 0 := by simp [integerDistance]

/-- `0 ≤ integerDistance x y`. -/
theorem integerDistance_nonneg (x y : ℝ) : 0 ≤ integerDistance x y := abs_nonneg _

/-- `integerDistance x y ≤ 1 / 2`: the distance to the nearest integer is at most a half
(mathlib's `abs_sub_round`). -/
theorem integerDistance_le_half (x y : ℝ) : integerDistance x y ≤ 1 / 2 := abs_sub_round (x - y)

/-- `integerDistance x y ≤ |x - y|`: the circle distance is at most the real distance. -/
theorem integerDistance_le_abs (x y : ℝ) : integerDistance x y ≤ |x - y| := by
  unfold integerDistance
  simpa using round_le (x - y) 0

/-- `integerDistance x y = integerDistance y x`. -/
theorem integerDistance_comm (x y : ℝ) : integerDistance x y = integerDistance y x := by
  have h1 : integerDistance x y ≤ integerDistance y x := by
    have := round_le (x - y) (-round (y - x))
    have he : x - y - ((-round (y - x) : ℤ) : ℝ) = -(y - x - round (y - x)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  have h2 : integerDistance y x ≤ integerDistance x y := by
    have := round_le (y - x) (-round (x - y))
    have he : y - x - ((-round (x - y) : ℤ) : ℝ) = -(x - y - round (x - y)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  exact le_antisymm h1 h2

/-- `integerDistance (x + n) y = integerDistance x y` for every integer `n`. -/
theorem integerDistance_add_int_left (x y : ℝ) (n : ℤ) : integerDistance (x + n) y = integerDistance x y := by
  unfold integerDistance
  have hxy : x + (n : ℝ) - y = (x - y) + (n : ℝ) := by ring
  rw [hxy, round_add_intCast]
  congr 1
  push_cast
  ring

/-- `integerDistance x (y + n) = integerDistance x y` for every integer `n`. -/
theorem integerDistance_add_int_right (x y : ℝ) (n : ℤ) : integerDistance x (y + n) = integerDistance x y := by
  rw [integerDistance_comm x (y + n), integerDistance_add_int_left y x n, integerDistance_comm]

/-- The triangle inequality `integerDistance x z ≤ integerDistance x y + integerDistance y z`. -/
theorem integerDistance_triangle (x y z : ℝ) : integerDistance x z ≤ integerDistance x y + integerDistance y z := by
  unfold integerDistance
  have h1 : |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| :=
    round_le (x - z) (round (x - y) + round (y - z))
  have h2 : x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)
      = (x - y - round (x - y)) + (y - z - round (y - z)) := by push_cast; ring
  calc |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| := h1
    _ = |(x - y - round (x - y)) + (y - z - round (y - z))| := by rw [h2]
    _ ≤ |x - y - round (x - y)| + |y - z - round (y - z)| := abs_add_le _ _

/-- `integerDistance x y = 0 ↔ ∃ n : ℤ, x - y = n`: the circle distance vanishes exactly when
`x - y` is an integer. -/
theorem integerDistance_eq_zero_iff (x y : ℝ) : integerDistance x y = 0 ↔ ∃ n : ℤ, x - y = n := by
  unfold integerDistance
  rw [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round (x - y), h⟩
  · rintro ⟨n, hn⟩
    rw [hn, round_intCast]


end WaveTurbulence.NumberTheory
