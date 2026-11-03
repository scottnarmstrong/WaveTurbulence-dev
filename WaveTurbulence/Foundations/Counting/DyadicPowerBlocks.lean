/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DyadicBlocks
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Dyadic power-profile sums

The endpoint-distance partition is additive in an arbitrary commutative
monoid, hence applies to complex exponential sums. Geometric weights with
positive exponent have a bounded total without any logarithmic loss.
-/

public section

namespace WaveTurbulence.Counting

/-- The exact dyadic partition, for real or complex summands. -/
theorem sum_eq_low_add_dyadic_blocks_addCommMonoid {ι α : Type*} [AddCommMonoid α]
    (s : Finset ι) (height : ι → ℝ) (F : ι → α)
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


/-- Finite geometric tails are bounded independently of the number of
blocks. The first weight is `q`, rather than one. -/
theorem sum_geometric_successor_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    (∑ j ∈ Finset.range J, q^(j+1)) ≤ q/(1-q) := by
  have he : (∑ j ∈ Finset.range J, q^(j+1)) = q*(∑ j ∈ Finset.range J, q^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ,mul_comm]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  rw [he,mul_assoc,geom_sum_mul_neg]
  nlinarith only [mul_nonneg hq (pow_nonneg hq J)]

/-- Combining actual complex dyadic-block estimates loses only the finite
geometric factor. This helper concerns sums, not an exponent-pair notion. -/
theorem norm_sum_le_of_dyadic_geometric_bounds {ι : Type*} (s : Finset ι)
    (height : ι → ℝ) (F : ι → ℂ) {R A B q : ℝ} (J : ℕ)
    (hR : 0 ≤ R) (hheight : ∀ i ∈ s, height i ≤ R)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1)
    (hlow : ‖∑ i ∈ s.filter (fun i => height i ≤ R/(2:ℝ)^J), F i‖ ≤ B)
    (hblock : ∀ j < J,
      ‖∑ i ∈ s.filter (fun i => R/(2:ℝ)^(j+1) < height i ∧
        height i ≤ R/(2:ℝ)^j), F i‖ ≤ A*q^(j+1)) :
    ‖∑ i ∈ s, F i‖ ≤ B+A*(q/(1-q)) := by
  classical
  rw [sum_eq_low_add_dyadic_blocks_addCommMonoid s height F hR hheight J]
  apply (norm_add_le _ _).trans
  apply add_le_add hlow
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ‖∑ i ∈ s.filter (fun i => R/(2:ℝ)^(j+1) < height i ∧
          height i ≤ R/(2:ℝ)^j), F i‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, A*q^(j+1) :=
      Finset.sum_le_sum (fun j hj => hblock j (Finset.mem_range.mp hj))
    _ = A*(∑ j ∈ Finset.range J, q^(j+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(q/(1-q)) := mul_le_mul_of_nonneg_left (sum_geometric_successor_le hq hq1 J) hA

end WaveTurbulence.Counting
