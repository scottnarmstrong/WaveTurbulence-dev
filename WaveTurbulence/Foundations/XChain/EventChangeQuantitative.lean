/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeBounds
public import WaveTurbulence.Foundations.Probability.CumulantMomentBounds
/-! Quantitative S7: the square-root event loss survives the whole cumulant expansion. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

/-- The number of error-bearing block selections has only exponential growth. -/
theorem card_error_selections_le {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) : (P.parts.powerset.erase ∅).card ≤ 2 ^ s.card := by
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    ((Finset.card_powerset _).le.trans (Nat.pow_le_pow_right (by decide) P.card_parts_le_card))

/-- Explicit event-change bound, with factorial moment losses and an exponential subset loss.
No arbitrary constant depending on the growing cumulant order is hidden. -/
theorem norm_cumulant_event_change_le {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A)
    (hi : ∀ J ⊆ s, IntegrableOn (fun ω => ∏ j ∈ J, X j ω) A μ)
    (C : ℕ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hold : ∀ J ⊆ s, J.Nonempty →
      ‖∫ ω in A, ∏ j ∈ J, X j ω ∂μ‖ ≤ (C * J.card).factorial * M ^ J.card)
    (herr : ∀ J ⊆ s, J.Nonempty →
      ‖∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ‖ ≤ ε * ((C * J.card).factorial * M ^ J.card)) :
    ‖cumulant (μ.restrict B) X s - cumulant (μ.restrict A) X s‖ ≤
      ε * 2 ^ s.card * ((C + 2) * s.card).factorial * M ^ s.card := by
  classical
  let K : ℝ := (C * s.card).factorial * M ^ s.card
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let W := fun J : Finset ι => ((C * J.card).factorial : ℝ) * M ^ J.card
  have hw (P : Finpartition s) : (∏ J ∈ P.parts, W J) ≤ K := by
    dsimp only [W, K]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, P.sum_card_parts]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Probability.prod_factorial_parts_le P C) (pow_nonneg hM _)
  have hinner (P : Finpartition s) :
      ‖∑ T ∈ P.parts.powerset.erase ∅, (-1 : ℂ) ^ T.card *
        (∏ J ∈ P.parts \ T, ∫ ω in A, ∏ j ∈ J, X j ω ∂μ) *
        ∏ J ∈ T, ∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ‖ ≤
          (2 ^ s.card : ℝ) * (ε * K) := by
    calc
      _ ≤ ∑ T ∈ P.parts.powerset.erase ∅, ‖(-1 : ℂ) ^ T.card *
          (∏ J ∈ P.parts \ T, ∫ ω in A, ∏ j ∈ J, X j ω ∂μ) *
          ∏ J ∈ T, ∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ _T ∈ P.parts.powerset.erase ∅, ε * K := by
        apply Finset.sum_le_sum
        intro T hT
        rw [mul_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2
        have hne := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hT).1
        exact (error_block_product_bound P.parts T hsub hne _ _ W hε1
          (fun J _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _))
          (fun J hJ => hold J (P.le hJ) (P.nonempty_of_mem_parts hJ))
          (fun J hJ => herr J (P.le hJ) (P.nonempty_of_mem_parts hJ))).trans
          (mul_le_mul_of_nonneg_left (hw P) hε)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hε hK)
        exact_mod_cast card_error_selections_le P
  rw [cumulant_event_change μ X s hB hBA hi]
  calc
    _ ≤ ∑ P : Finpartition s, ‖(-1 : ℂ) ^ (P.parts.card - 1) *
        ((P.parts.card - 1).factorial : ℂ) *
        ∑ T ∈ P.parts.powerset.erase ∅, (-1 : ℂ) ^ T.card *
          (∏ J ∈ P.parts \ T, ∫ ω in A, ∏ j ∈ J, X j ω ∂μ) *
          ∏ J ∈ T, ∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ _P : Finpartition s, (s.card.factorial : ℝ) * (2 ^ s.card * (ε * K)) := by
      apply Finset.sum_le_sum
      intro P _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le ((Nat.sub_le _ _).trans P.card_parts_le_card)
      · exact hinner P
      · exact norm_nonneg _
      · positivity
    _ = ε * 2 ^ s.card *
        ((Fintype.card (Finpartition s) * s.card.factorial * (C * s.card).factorial : ℕ) : ℝ) *
        M ^ s.card := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K, Nat.cast_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast Probability.partition_factorial_loss (s := s) C)
        (mul_nonneg hε (pow_nonneg (by norm_num) _))

end WaveTurbulence.Induct
