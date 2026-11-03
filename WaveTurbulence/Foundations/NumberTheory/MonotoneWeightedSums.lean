/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Finite Abel bounds for decreasing real weights

Bounded actual prefix sums control a sum with a nonnegative decreasing
weight by the initial weight. Only prefixes of the specified finite range
are needed. This supplies the amplitude step in the circle B application.
-/

public section

namespace WaveTurbulence.NumberTheory

open Finset

/-- Finite Abel inequality in a real normed space. -/
theorem norm_sum_smul_le_of_prefix_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → E) (b : ℕ → ℝ) (N : ℕ) {B : ℝ}
    (hS : ∀ k ≤ N, ‖∑ i ∈ range k, u i‖ ≤ B)
    (hb : ∀ i ≤ N, 0 ≤ b i)
    (hanti : ∀ i j, i ≤ j → j < N → b j ≤ b i) :
    ‖∑ i ∈ range N, b i • u i‖ ≤ B*b 0 := by
  by_cases hN : N = 0
  · subst N
    have hB : 0 ≤ B := by simpa using hS 0 (by omega)
    simpa only [sum_range_zero, norm_zero] using mul_nonneg hB (hb 0 le_rfl)
  have hNm : N-1 < N := by omega
  have hB : 0 ≤ B := by simpa using hS 0 (by omega)
  rw [sum_range_by_parts]
  have hfirst : ‖b (N-1) • ∑ i ∈ range N, u i‖ ≤ B*b (N-1) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb _ (Nat.le_of_lt hNm)),mul_comm]
    exact mul_le_mul_of_nonneg_right (hS N le_rfl) (hb _ (Nat.le_of_lt hNm))
  have hrest : ‖∑ i ∈ range (N-1), (b (i+1)-b i) • ∑ j ∈ range (i+1), u j‖ ≤
      B*(b 0-b (N-1)) := by
    calc
      _ ≤ ∑ i ∈ range (N-1), ‖(b (i+1)-b i) • ∑ j ∈ range (i+1), u j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (N-1), (b i-b (i+1))*B := by
        apply sum_le_sum
        intro i hi
        have hiN : i+1 < N := by have := mem_range.mp hi; omega
        have hdec := hanti i (i+1) (by omega) hiN
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hdec),neg_sub]
        exact mul_le_mul_of_nonneg_left (hS (i+1) (by omega)) (sub_nonneg.mpr hdec)
      _ = B*(b 0-b (N-1)) := by rw [← sum_mul,sum_range_sub']; ring
  exact (norm_sub_le _ _).trans ((add_le_add hfirst hrest).trans_eq (by ring))

/-- Reindex an integer interval by its consecutive natural sample indices. -/
theorem sum_Ioc_add_nat_eq_range {E : Type*} [AddCommMonoid E]
    (u : ℤ → E) (a : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc a (a+N), u n = ∑ i ∈ range N, u (a+i+1) := by
  symm
  apply sum_bij (fun (i : ℕ) _ => a+(i:ℤ)+1)
  · intro i hi
    have hiN := mem_range.mp hi
    simp only [mem_Ioc]
    constructor <;> omega
  · intro i hi j hj hij
    omega
  · intro n hn
    simp only [mem_Ioc] at hn
    refine ⟨(n-a-1).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-- Finite Abel inequality on an actual integer interval. -/
theorem norm_sum_Ioc_smul_le_of_prefix_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℤ → E) (b : ℤ → ℝ) (a : ℤ) (N : ℕ) {B : ℝ}
    (hS : ∀ k ≤ N, ‖∑ i ∈ Ioc a (a+k), u i‖ ≤ B)
    (hb : ∀ i ∈ Icc (a+1) (a+N+1), 0 ≤ b i)
    (hanti : AntitoneOn b (Set.Ici (a+1))) :
    ‖∑ i ∈ Ioc a (a+N), b i • u i‖ ≤ B*b (a+1) := by
  simp_rw [sum_Ioc_add_nat_eq_range] at hS ⊢
  simpa only [Nat.cast_zero,add_zero] using! norm_sum_smul_le_of_prefix_bound (fun i => u (a+i+1)) (fun i => b (a+i+1)) N
    hS (fun i hi => hb _ (by simp only [mem_Icc]; constructor <;> omega))
    (fun i j hij _hj => hanti (by simp only [Set.mem_Ici]; omega)
      (by simp only [Set.mem_Ici]; omega) (by omega))

end WaveTurbulence.NumberTheory
