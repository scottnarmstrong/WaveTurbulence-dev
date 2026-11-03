/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeDisc
import Mathlib.Tactic
/-!
# Reindexing integer sample intervals

Exact reindexing identities for the circle counting estimates.
-/

public section

namespace WaveTurbulence.Counting
/-- Integer samples as a translated natural range, including empty intervals. -/
theorem sum_int_Icc_eq_range (F : ℝ → ℝ) (L U : ℤ) :
    (∑ x ∈ Finset.Icc L U, F x) =
      ∑ k ∈ Finset.range (U+1-L).toNat, F ((L:ℝ)+k) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  change F ((L+(k:ℤ):ℤ):ℝ) = _
  rw [Int.cast_add, Int.cast_natCast]
/-- Shift a zero-based range to a positive half-open integer interval. -/
theorem sum_range_eq_Ioc (F : ℝ → ℝ) (N : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range N, F (t+k)) =
      ∑ k ∈ Finset.Ioc 0 N, F ((k:ℝ)+(t-1)) := by
  apply Finset.sum_bij (fun k _ => k+1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ioc]
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    simp only [Finset.mem_Ioc] at hb
    refine ⟨b-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    congr 1
    push_cast
    ring

end WaveTurbulence.Counting
