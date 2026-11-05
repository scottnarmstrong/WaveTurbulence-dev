/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SmallCumulantBound
/-! The moment-cumulant inversion retains each individual spatial weight. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem norm_moment_le_of_weighted_cumulants {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) (hs : s.Nonempty)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (h : ∀ A ⊆ s, A.Nonempty →
      ‖cumulant μ X A‖ ≤ ((C * A.card).factorial : ℝ) * ∏ i ∈ A, M i) :
    ‖∫ ω, ∏ i ∈ s, X i ω ∂μ‖ ≤ (((C + 2) * s.card).factorial : ℝ) * ∏ i ∈ s, M i := by
  classical
  let K : ℝ := ((C * s.card).factorial : ℝ) * ∏ i ∈ s, M i
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (prod_nonneg (fun i _ => hM i))
  have hp (P : Finpartition s) : ‖∏ A ∈ P.parts, cumulant μ X A‖ ≤ K := by
    rw [norm_prod]
    calc
      _ ≤ ∏ A ∈ P.parts, (((C * A.card).factorial : ℝ) * ∏ i ∈ A, M i) :=
        prod_le_prod₀ (fun A _ => norm_nonneg _)
          (fun A hA => h A (P.le hA) (P.nonempty_of_mem_parts hA))
      _ = (∏ A ∈ P.parts, ((C * A.card).factorial : ℝ)) * ∏ i ∈ s, M i := by
        rw [prod_mul_distrib, prod_finpartition_parts]
      _ ≤ K := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Probability.prod_factorial_parts_le P C) (prod_nonneg (fun i _ => hM i))
  rw [integral_prod_eq_sum_cumulant μ X s hs]
  calc
    _ ≤ ∑ P : Finpartition s, K := (norm_sum_le _ _).trans (sum_le_sum (fun P _ => hp P))
    _ ≤ ∑ P : Finpartition s, (s.card.factorial : ℝ) * K := by
      apply sum_le_sum
      intro P _
      exact le_mul_of_one_le_left hK (by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos s.card)))
    _ = ((Fintype.card (Finpartition s) * s.card.factorial * (C * s.card).factorial : ℕ) : ℝ) *
        ∏ i ∈ s, M i := by
      simp only [sum_const, card_univ, nsmul_eq_mul, K, Nat.cast_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Probability.partition_factorial_loss (s := s) C) (prod_nonneg (fun i _ => hM i))

end WaveTurbulence.Induct
