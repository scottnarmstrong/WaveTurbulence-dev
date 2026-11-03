/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.ReciprocalTail
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Telescoping the endpoint tail

At integer spatial endpoints the Poisson characters are all one.
The reciprocal tail can therefore be paired and telescoped without
estimating its positive and negative parts separately.
-/

public section

namespace WaveTurbulence.VdCB

/-- A shifted finite reciprocal difference is bounded by its initial
harmonic block, independently of the upper cutoff. -/
theorem sum_range_reciprocal_sub_shift_le (K m : ℕ) :
    (∑ j ∈ Finset.range K, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + m + 1))) ≤
      ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 1) := by
  have hle : (∑ j ∈ Finset.range K, 1 / ((j : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range (m + K), 1 / ((j : ℝ) + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro j _ _
    positivity
  rw [Finset.sum_range_add] at hle
  have heq : (∑ j ∈ Finset.range K, 1 / (((m + j : ℕ) : ℝ) + 1)) =
      ∑ j ∈ Finset.range K, 1 / ((j : ℝ) + m + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  rw [heq] at hle
  rw [Finset.sum_sub_distrib]
  linarith only [hle]

/-- The naturally paired one-sided tail is bounded by one harmonic block
of the derivative-range width. -/
theorem abs_sum_range_shifted_reciprocal_pair_le {r : ℝ} {N : ℕ}
    (hr : 0 ≤ r) (hrN : r ≤ N) (K : ℕ) :
    |∑ j ∈ Finset.range K,
      (1 / (r + j + 1) - 1 / ((N : ℝ) - r + j + 1))| ≤
      ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 1) := by
  have hpoint (j : ℕ) :
      -(1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + N + 1)) ≤
        1 / (r + j + 1) - 1 / ((N : ℝ) - r + j + 1) ∧
      1 / (r + j + 1) - 1 / ((N : ℝ) - r + j + 1) ≤
        1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + N + 1) := by
    have hj : 0 < (j : ℝ) + 1 := by positivity
    have h1 : 1 / ((j : ℝ) + N + 1) ≤ 1 / (r + j + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : 1 / (r + j + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le hj (by linarith)
    have h3 : 1 / ((j : ℝ) + N + 1) ≤ 1 / ((N : ℝ) - r + j + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have h4 : 1 / ((N : ℝ) - r + j + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le hj (by linarith)
    constructor <;> linarith only [h1, h2, h3, h4]
  apply abs_le.mpr
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.range K) (fun j _ => (hpoint j).1)
    rw [Finset.sum_neg_distrib] at hh
    linarith only [hh, sum_range_reciprocal_sub_shift_le K N]
  · exact (Finset.sum_le_sum (fun j _ => (hpoint j).2)).trans
      (sum_range_reciprocal_sub_shift_le K N)

/-- The endpoint tail bound has logarithmic dependence on the range width. -/
theorem abs_sum_range_shifted_reciprocal_pair_le_log {r : ℝ} {N : ℕ}
    (hr : 0 ≤ r) (hrN : r ≤ N) (K : ℕ) :
    |∑ j ∈ Finset.range K,
      (1 / (r + j + 1) - 1 / ((N : ℝ) - r + j + 1))| ≤ 1 + Real.log N := by
  apply (abs_sum_range_shifted_reciprocal_pair_le hr hrN K).trans
  have hh := harmonic_le_one_add_log N
  simpa only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Nat.cast_add,
    Nat.cast_one, one_div] using hh

end WaveTurbulence.VdCB
