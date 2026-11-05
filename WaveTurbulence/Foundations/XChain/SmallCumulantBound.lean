/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeBounds
public import WaveTurbulence.Foundations.Probability.CumulantMomentBounds
/-! A small factor survives the complete cumulant moment conversion, with explicit factorial loss. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem norm_cumulant_le_of_small_variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {i : ι} (hi : i ∈ s)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) {ε : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ J ⊆ s, J.Nonempty →
      ‖∫ ω, ∏ j ∈ J, X j ω ∂μ‖ ≤ (C * J.card).factorial * ∏ j ∈ J, M j)
    (hsmall : ∀ J ⊆ s, i ∈ J →
      ‖∫ ω, ∏ j ∈ J, X j ω ∂μ‖ ≤ ε * ((C * J.card).factorial * ∏ j ∈ J, M j)) :
    ‖cumulant μ X s‖ ≤ ε * ((C + 2) * s.card).factorial * ∏ j ∈ s, M j := by
  classical
  let W := fun J : Finset ι => ((C * J.card).factorial : ℝ) * ∏ j ∈ J, M j
  let K : ℝ := (C * s.card).factorial * ∏ j ∈ s, M j
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)
  have hw (P : Finpartition s) : (∏ J ∈ P.parts, W J) ≤ K := by
    dsimp only [W, K]
    rw [prod_mul_distrib, prod_finpartition_parts]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Probability.prod_factorial_parts_le P C)
      (prod_nonneg fun j _ => hM j)
  have hp (P : Finpartition s) :
      ‖∏ J ∈ P.parts, ∫ ω, ∏ j ∈ J, X j ω ∂μ‖ ≤ ε * K := by
    rw [norm_prod]
    have hpart : P.part i ∈ P.parts := P.part_mem.mpr hi
    exact (prod_le_small_factor P.parts _ W hpart (fun _ _ => norm_nonneg _)
      (fun J hJ => hmom J (P.le hJ) (P.nonempty_of_mem_parts hJ))
      (hsmall (P.part i) (P.le hpart) (P.mem_part hi))).trans
      (mul_le_mul_of_nonneg_left (hw P) hε)
  have ht (P : Finpartition s) :
      ‖(-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
        ∏ J ∈ P.parts, ∫ ω, ∏ j ∈ J, X j ω ∂μ‖ ≤ s.card.factorial * (ε * K) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le ((Nat.sub_le _ _).trans P.card_parts_le_card))
      (hp P) (norm_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ P : Finpartition s, ‖(-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
        ∏ J ∈ P.parts, ∫ ω, ∏ j ∈ J, X j ω ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ _P : Finpartition s, (s.card.factorial : ℝ) * (ε * K) := sum_le_sum fun P _ => ht P
    _ = ε * ((Fintype.card (Finpartition s) * s.card.factorial * (C * s.card).factorial : ℕ) : ℝ) *
        ∏ j ∈ s, M j := by
      simp only [sum_const, card_univ, nsmul_eq_mul, K, Nat.cast_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Probability.partition_factorial_loss (s := s) C) hε)
      (prod_nonneg fun j _ => hM j)

end WaveTurbulence.Induct
