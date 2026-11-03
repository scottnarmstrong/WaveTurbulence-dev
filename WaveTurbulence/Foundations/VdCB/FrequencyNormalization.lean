/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Canonical integer normalization of a derivative interval

Floor at the lower endpoint and ceiling at the upper endpoint give a
natural frequency count bounded by the interval width plus two.
-/

public section

namespace WaveTurbulence.VdCB

/-- Integer normalization introduces at most two frequencies beyond the
actual real interval width. This is numerical data, not an analytic premise. -/
theorem exists_frequency_normalization {A B : ℝ} (hAB : A ≤ B) :
    ∃ m : ℤ, ∃ N : ℕ,
      (m : ℝ) ≤ A ∧ A < m + 1 ∧ (m : ℝ) + N - 1 < B ∧ B ≤ m + N ∧
        (N : ℝ) ≤ B - A + 2 := by
  let m : ℤ := ⌊A⌋
  have hmc : m ≤ ⌈B⌉ := by
    have hh : (m : ℝ) ≤ (⌈B⌉ : ℝ) := (Int.floor_le A).trans (hAB.trans (Int.le_ceil B))
    exact_mod_cast hh
  let N : ℕ := (⌈B⌉ - m).toNat
  have hNint : (N : ℤ) = ⌈B⌉ - m := Int.toNat_of_nonneg (sub_nonneg.mpr hmc)
  have hNreal : (N : ℝ) = (⌈B⌉ : ℝ) - (m : ℝ) := by exact_mod_cast hNint
  have hfloor := Int.floor_le A
  have hfloorlt := Int.lt_floor_add_one A
  have hceil := Int.le_ceil B
  have hceillt := Int.ceil_lt_add_one B
  refine ⟨m, N, hfloor, hfloorlt, ?_, ?_, ?_⟩
  · rw [hNreal]
    linarith only [hceillt]
  · rw [hNreal]
    linarith only [hceil]
  · rw [hNreal]
    change (⌈B⌉ : ℝ) - (⌊A⌋ : ℝ) ≤ B - A + 2
    linarith only [hfloorlt, hceillt]

end WaveTurbulence.VdCB
