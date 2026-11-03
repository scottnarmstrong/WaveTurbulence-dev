/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Finite dyadic height blocks

Numerical covering, uniqueness, and summation facts for the global circular
arc decomposition in NT-CIRCLE-v2 goal 2. The lower endpoints of the blocks
are open and the upper endpoints closed, giving a disjoint classification.
-/

public section

namespace WaveTurbulence.Counting

/-- Each height above the terminal cutoff belongs to a dyadic block. -/
theorem exists_dyadic_height_block {R y : ℝ} (J : ℕ)
    (hlo : R / (2 : ℝ) ^ J < y) (hhi : y ≤ R) :
    ∃ j : ℕ, j < J ∧ R / (2 : ℝ) ^ (j + 1) < y ∧ y ≤ R / (2 : ℝ) ^ j := by
  induction J with
  | zero => simp only [pow_zero, div_one] at hlo; exact (not_lt_of_ge hhi hlo).elim
  | succ J ih =>
      by_cases hy : R / (2 : ℝ) ^ J < y
      · obtain ⟨j, hj, hlow, hhigh⟩ := ih hy
        exact ⟨j, Nat.lt_succ_of_lt hj, hlow, hhigh⟩
      · exact ⟨J, Nat.lt_succ_self J, hlo, le_of_not_gt hy⟩

/-- Two different dyadic height blocks have disjoint membership intervals. -/
theorem dyadic_height_block_index_unique {R y : ℝ} (hR : 0 ≤ R) {i j : ℕ}
    (hi : R / (2 : ℝ) ^ (i + 1) < y ∧ y ≤ R / (2 : ℝ) ^ i)
    (hj : R / (2 : ℝ) ^ (j + 1) < y ∧ y ≤ R / (2 : ℝ) ^ j) : i = j := by
  have hnot (i j : ℕ) (hij : i < j)
      (hi : R / (2 : ℝ) ^ (i + 1) < y)
      (hj : y ≤ R / (2 : ℝ) ^ j) : False := by
    have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij)
    have hdiv := div_le_div_of_nonneg_left hR (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    exact (not_lt_of_ge (hj.trans hdiv)) hi
  rcases lt_trichotomy i j with h | h | h
  · exact (hnot i j h hi.1 hj.2).elim
  · exact h
  · exact (hnot j i h hj.1 hi.2).elim

/-- Exact sum of the lower heights of the dyadic blocks. -/
theorem sum_dyadic_heights (R : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, R / (2 : ℝ) ^ (j + 1)) = R - R / (2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring

/-- Dyadic block heights have total at most the radius. -/
theorem sum_dyadic_heights_le {R : ℝ} (hR : 0 ≤ R) (J : ℕ) :
    (∑ j ∈ Finset.range J, R / (2 : ℝ) ^ (j + 1)) ≤ R := by
  rw [sum_dyadic_heights]
  exact sub_le_self _ (div_nonneg hR (by positivity))

/-- For radius `r³`, choose the final cutoff between `r²` and `2r²`.
Every preceding dyadic lower height is then at least `r²`. -/
theorem exists_dyadic_circle_cutoff {r : ℝ} (hr : 1 ≤ r) :
    ∃ J : ℕ, r ^ 2 ≤ r ^ 3 / (2 : ℝ) ^ J ∧
      r ^ 3 / (2 : ℝ) ^ J < 2 * r ^ 2 := by
  obtain ⟨J, hlo, hhi⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hp : 0 < (2 : ℝ) ^ J := by positivity
  refine ⟨J, ?_, ?_⟩
  · rw [le_div_iff₀ hp]
    have h := mul_le_mul_of_nonneg_left hlo (sq_nonneg r)
    nlinarith only [h]
  · rw [div_lt_iff₀ hp]
    rw [pow_succ] at hhi
    have h := mul_lt_mul_of_pos_left hhi (sq_pos_of_pos hrpos)
    nlinarith only [h]

/-- Exact partition of a finite sum into its low-height part and its disjoint
dyadic blocks. Heights at a dyadic boundary are assigned to the lower block. -/
theorem sum_eq_low_add_dyadic_blocks {ι : Type*} (s : Finset ι) (height F : ι → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hheight : ∀ i ∈ s, height i ≤ R) (J : ℕ) :
    (∑ i ∈ s, F i) =
      (∑ i ∈ s.filter (fun i => height i ≤ R / (2 : ℝ) ^ J), F i) +
      ∑ j ∈ Finset.range J,
        ∑ i ∈ s.filter (fun i => R / (2 : ℝ) ^ (j + 1) < height i ∧
          height i ≤ R / (2 : ℝ) ^ j), F i := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hlo : height i ≤ R / (2 : ℝ) ^ J
  · have hz : ∑ j ∈ Finset.range J,
        (if R / (2 : ℝ) ^ (j + 1) < height i ∧ height i ≤ R / (2 : ℝ) ^ j then F i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
        pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hj)
      have hdiv := div_le_div_of_nonneg_left hR (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
      apply ite_eq_right
      intro hblock
      exact (not_lt_of_ge (hlo.trans hdiv)) hblock.1
    rw [ite_eq_left hlo, hz, add_zero]
  · obtain ⟨j, hj, hlow, hhigh⟩ := exists_dyadic_height_block J (lt_of_not_ge hlo) (hheight i hi)
    rw [ite_eq_right hlo, zero_add, Finset.sum_eq_single j]
    · rw [ite_eq_left ⟨hlow, hhigh⟩]
    · intro k _ hkj
      apply ite_eq_right
      intro hk
      exact hkj (dyadic_height_block_index_unique hR hk ⟨hlow, hhigh⟩)
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr hj)).elim

end WaveTurbulence.Counting
