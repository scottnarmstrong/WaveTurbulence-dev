/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Inversion
public import WaveTurbulence.Foundations.Combinatorics.PartitionCount
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Factorial moment–cumulant bounds

TARGET L813–L815 uses the finite partition identities to exchange moments and
cumulants with `(C₀ R)!` losses. Here blockwise bounds with constant `C₀` yield
whole-set bounds with constant `C₀+2`. The underlying measure can be restricted
and need not be normalized. These are conditional bounds, not assertions of
moment estimates for a particular random field.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory Finset
open scoped Classical

variable {ι : Type*} [DecidableEq ι] {s : Finset ι}

/-- Products of the factorial block losses are bounded by the total factorial. -/
lemma prod_factorial_parts_le (P : Finpartition s) (C₀ : ℕ) :
    ∏ A ∈ P.parts, (C₀ * A.card).factorial ≤ (C₀ * s.card).factorial := by
  have h := Nat.le_of_dvd (Nat.factorial_pos (∑ A ∈ P.parts, C₀ * A.card))
    (Nat.prod_factorial_dvd_factorial_sum P.parts (fun A => C₀ * A.card))
  simpa only [← mul_sum, P.sum_card_parts] using h

/-- A partition product preserves the exponential weight and factorial loss. -/
lemma norm_prod_partition_le (P : Finpartition s) (F : Finset ι → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (C₀ : ℕ)
    (hF : ∀ A ∈ P.parts, ‖F A‖ ≤ (C₀ * A.card).factorial * B ^ A.card) :
    ‖∏ A ∈ P.parts, F A‖ ≤ (C₀ * s.card).factorial * B ^ s.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ A ∈ P.parts, ((C₀ * A.card).factorial : ℝ) * B ^ A.card :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) hF
    _ = (∏ A ∈ P.parts, ((C₀ * A.card).factorial : ℝ)) * B ^ s.card := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, P.sum_card_parts]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast prod_factorial_parts_le P C₀) (pow_nonneg hB _)

/-- The partition-count and coefficient losses can be absorbed into two extra factorial units. -/
lemma partition_factorial_loss (C₀ : ℕ) :
    Fintype.card (Finpartition s) * s.card.factorial * (C₀ * s.card).factorial ≤
      ((C₀ + 2) * s.card).factorial := by
  calc
    _ ≤ (2 * s.card).factorial * (C₀ * s.card).factorial :=
      Nat.mul_le_mul_right _ Combinatorics.card_finpartition_mul_factorial_le
    _ ≤ (2 * s.card + C₀ * s.card).factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
    _ = _ := by congr 1; ring

/-- Conditional conversion of blockwise factorial moment bounds to a cumulant bound. -/
theorem norm_cumulant_le_of_moment_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ι → Ω → ℂ) {B : ℝ} (hB : 0 ≤ B) (C₀ : ℕ)
    (hM : ∀ A ⊆ s, A.Nonempty →
      ‖∫ ω, ∏ j ∈ A, X j ω ∂μ‖ ≤ (C₀ * A.card).factorial * B ^ A.card) :
    ‖cumulant μ X s‖ ≤ ((C₀ + 2) * s.card).factorial * B ^ s.card := by
  let K : ℝ := (C₀ * s.card).factorial * B ^ s.card
  have hK : 0 ≤ K := by positivity
  have hterm (P : Finpartition s) :
      ‖(-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
        ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ‖ ≤ s.card.factorial * K := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le ((Nat.sub_le _ _).trans P.card_parts_le_card)
    · exact norm_prod_partition_le P _ hB C₀
        (fun A hA => hM A (P.le hA) (P.nonempty_of_mem_parts hA))
    · positivity
    · positivity
  calc
    _ ≤ ∑ P : Finpartition s, ‖(-1 : ℂ) ^ (P.parts.card - 1) *
        ((P.parts.card - 1).factorial : ℂ) * ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _P : Finpartition s, (s.card.factorial : ℝ) * K := sum_le_sum (fun P _ => hterm P)
    _ = ((Fintype.card (Finpartition s) * s.card.factorial * (C₀ * s.card).factorial : ℕ) : ℝ) *
        B ^ s.card := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast partition_factorial_loss (s := s) C₀)
      (pow_nonneg hB _)

/-- Conditional conversion of blockwise factorial cumulant bounds to a moment bound. -/
theorem norm_moment_le_of_cumulant_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (hs : s.Nonempty) {B : ℝ} (hB : 0 ≤ B) (C₀ : ℕ)
    (hK : ∀ A ⊆ s, A.Nonempty → ‖cumulant μ X A‖ ≤ (C₀ * A.card).factorial * B ^ A.card) :
    ‖∫ ω, ∏ j ∈ s, X j ω ∂μ‖ ≤ ((C₀ + 2) * s.card).factorial * B ^ s.card := by
  rw [integral_prod_eq_sum_cumulant μ X s hs]
  have hprod (P : Finpartition s) : ‖∏ A ∈ P.parts, cumulant μ X A‖ ≤
      (C₀ * s.card).factorial * B ^ s.card :=
    norm_prod_partition_le P _ hB C₀
      (fun A hA => hK A (P.le hA) (P.nonempty_of_mem_parts hA))
  calc
    _ ≤ ∑ P : Finpartition s, ‖∏ A ∈ P.parts, cumulant μ X A‖ := norm_sum_le _ _
    _ ≤ ∑ _P : Finpartition s, ((C₀ * s.card).factorial : ℝ) * B ^ s.card :=
      sum_le_sum (fun P _ => hprod P)
    _ ≤ ∑ _P : Finpartition s, (s.card.factorial : ℝ) *
        ((C₀ * s.card).factorial * B ^ s.card) := by
      apply sum_le_sum
      intro P _
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos s.card)))
    _ = ((Fintype.card (Finpartition s) * s.card.factorial * (C₀ * s.card).factorial : ℕ) : ℝ) *
        B ^ s.card := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast partition_factorial_loss (s := s) C₀)
      (pow_nonneg hB _)

end WaveTurbulence.Probability
