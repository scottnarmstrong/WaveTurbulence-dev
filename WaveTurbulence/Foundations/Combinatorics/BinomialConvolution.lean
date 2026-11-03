/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A binomial convolution estimate

The scalar estimate underlying DH21 Lemma A.4 (`combineq`, L2814–L2822).
-/

public section

namespace WaveTurbulence.Combinatorics
open Finset

/-- The central binomial coefficient dominates `2^n`. -/
theorem two_pow_le_central_choose (n : ℕ) : 2 ^ n ≤ (2 * n).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq := Nat.succ_mul_centralBinom_succ n
    change (n + 1) * ((2 * (n + 1)).choose (n + 1)) =
      2 * (2 * n + 1) * ((2 * n).choose n) at heq
    rw [pow_succ]
    nlinarith [Nat.zero_le ((2 * n).choose n)]

/-- The middle summand of Vandermonde gives a square lower bound. -/
theorem choose_sq_le_double_choose (A B : ℕ) :
    A.choose B ^ 2 ≤ (2 * A).choose (2 * B) := by
  rw [two_mul A, Nat.add_choose_eq]
  have h := Finset.single_le_sum (fun p _ => Nat.zero_le (A.choose p.1 * A.choose p.2))
    (show (B, B) ∈ Finset.antidiagonal (2 * B) by simp [two_mul])
  simpa only [sq] using h

/-- On the lower half, the ratio in DH21 (A.4) decays geometrically. -/
theorem choose_ratio_le_geometric {A B : ℕ} (h : 2 * B ≤ A) :
    (A.choose B : ℝ) / (2 * A).choose (2 * B) ≤ (1 / 2 : ℝ) ^ B := by
  have hB : B ≤ A := by omega
  have hp : (0 : ℝ) < A.choose B := by exact_mod_cast Nat.choose_pos hB
  have hq : (0 : ℝ) < (2 * A).choose (2 * B) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 * B ≤ 2 * A)
  have hs : (A.choose B : ℝ) ^ 2 ≤ (2 * A).choose (2 * B) := by
    exact_mod_cast choose_sq_le_double_choose A B
  have hg : (2 : ℝ) ^ B ≤ A.choose B := by
    exact_mod_cast (two_pow_le_central_choose B).trans (Nat.choose_le_choose B h)
  calc
    (A.choose B : ℝ) / (2 * A).choose (2 * B) ≤ 1 / A.choose B := by
      apply (div_le_div_iff₀ hq hp).mpr
      nlinarith
    _ ≤ 1 / (2 : ℝ) ^ B := one_div_le_one_div_of_le (by positivity) hg
    _ = (1 / 2 : ℝ) ^ B := by rw [div_pow, one_pow]

/-- A symmetric geometric bound valid on the entire row. -/
theorem choose_ratio_le_geometric_add {A B : ℕ} (hB : B ≤ A) :
    (A.choose B : ℝ) / (2 * A).choose (2 * B) ≤
      (1 / 2 : ℝ) ^ B + (1 / 2 : ℝ) ^ (A - B) := by
  by_cases h : 2 * B ≤ A
  · exact (choose_ratio_le_geometric h).trans (le_add_of_nonneg_right (by positivity))
  have h' : 2 * (A - B) ≤ A := by omega
  have hsymm : (2 * A).choose (2 * (A - B)) = (2 * A).choose (2 * B) := by
    rw [Nat.mul_sub_left_distrib, Nat.choose_symm (by omega : 2 * B ≤ 2 * A)]
  have hc := choose_ratio_le_geometric h'
  rw [Nat.choose_symm hB, hsymm] at hc
  exact hc.trans (le_add_of_nonneg_left (by positivity))

/-- A finite geometric sum is bounded uniformly by two. -/
theorem sum_half_pow_le_two (N : ℕ) :
    ∑ i ∈ range N, (1 / 2 : ℝ) ^ i ≤ 2 := by
  have heq : ∑ i ∈ range N, (1 / 2 : ℝ) ^ i = 2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  have : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  linarith

/-- DH21 (A.4), equation `expdecay`: the sum of binomial ratios is at most four. -/
theorem sum_choose_ratio_le_four (A : ℕ) :
    ∑ B ∈ range (A + 1), (A.choose B : ℝ) / (2 * A).choose (2 * B) ≤ 4 := by
  calc
    _ ≤ ∑ B ∈ range (A + 1),
        ((1 / 2 : ℝ) ^ B + (1 / 2 : ℝ) ^ (A - B)) := by
      apply sum_le_sum
      intro B hB
      exact choose_ratio_le_geometric_add (by simpa using mem_range_succ_iff.mp hB)
    _ = (∑ B ∈ range (A + 1), (1 / 2 : ℝ) ^ B) +
        (∑ B ∈ range (A + 1), (1 / 2 : ℝ) ^ B) := by
      rw [sum_add_distrib]
      congr 1
      simpa using sum_range_reflect (fun B => (1 / 2 : ℝ) ^ B) (A + 1)
    _ ≤ 4 := by have h := sum_half_pow_le_two (A + 1); linarith

/-- Rewrite the factorial weight as a binomial ratio times the total factorial. -/
theorem factorial_weight_eq_ratio {A B : ℕ} (hB : B ≤ A) :
    (A.choose B : ℝ) * (2 * B).factorial * (2 * (A - B)).factorial =
      ((A.choose B : ℝ) / (2 * A).choose (2 * B)) * (2 * A).factorial := by
  have hq : (2 * A).choose (2 * B) ≠ 0 := Nat.choose_ne_zero (by omega)
  have heq := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * B ≤ 2 * A)
  rw [← Nat.mul_sub_left_distrib] at heq
  have heq' : ((2 * A).choose (2 * B) : ℝ) * (2 * B).factorial *
      (2 * (A - B)).factorial = (2 * A).factorial := by exact_mod_cast heq
  rw [← heq']
  field_simp

/-- The binary factorial convolution from DH21 Lemma A.4 has constant four. -/
theorem sum_choose_factorial_le (A : ℕ) :
    ∑ B ∈ range (A + 1), (A.choose B : ℝ) * (2 * B).factorial *
      (2 * (A - B)).factorial ≤ 4 * (2 * A).factorial := by
  calc
    _ = (∑ B ∈ range (A + 1), (A.choose B : ℝ) / (2 * A).choose (2 * B)) *
        (2 * A).factorial := by
      rw [sum_mul]
      apply sum_congr rfl
      intro B hB
      exact factorial_weight_eq_ratio (mem_range_succ_iff.mp hB)
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_choose_ratio_le_four A) (by positivity)

end WaveTurbulence.Combinatorics
