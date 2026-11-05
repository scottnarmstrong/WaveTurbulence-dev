/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeBounds
/-! Exact nonempty error-block expansion and its uniform exponentially counted product bound. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem prod_difference_eq_error_blocks {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i =
      ∑ T ∈ s.powerset.erase ∅, (-1 : ℂ) ^ T.card *
        (∏ i ∈ s \ T, g i) * ∏ i ∈ T, (g i - f i) := by
  have h := prod_sub_error_terms s g (fun i => g i - f i)
  have he : (∏ i ∈ s, (g i - (g i - f i))) = ∏ i ∈ s, f i :=
    prod_congr rfl (fun i _ => sub_sub_cancel _ _)
  exact (congrArg (fun z : ℂ => z - ∏ i ∈ s, g i) he).symm.trans h

theorem norm_prod_difference_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ)
    (M : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : ∀ i ∈ s, 0 ≤ M i) (hg : ∀ i ∈ s, ‖g i‖ ≤ M i)
    (herr : ∀ i ∈ s, ‖f i - g i‖ ≤ ε * M i) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ 2 ^ s.card * ε * ∏ i ∈ s, M i := by
  classical
  rw [prod_difference_eq_error_blocks]
  have h0 : 0 ≤ ε * ∏ i ∈ s, M i := mul_nonneg hε (prod_nonneg hM)
  calc
    _ ≤ ∑ T ∈ s.powerset.erase ∅, ‖(-1 : ℂ) ^ T.card *
        (∏ i ∈ s \ T, g i) * ∏ i ∈ T, (g i - f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _T ∈ s.powerset.erase ∅, ε * ∏ i ∈ s, M i := by
      apply sum_le_sum
      intro T hT
      rw [mul_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact error_block_product_bound s T (mem_powerset.mp (mem_erase.mp hT).2)
        (nonempty_iff_ne_empty.mpr (mem_erase.mp hT).1) g (fun i => g i - f i) M hε1 hM hg
        (fun i hi => (norm_sub_rev (g i) (f i)).le.trans (herr i hi))
    _ ≤ 2 ^ s.card * ε * ∏ i ∈ s, M i := by
      rw [sum_const, nsmul_eq_mul, mul_assoc]
      apply mul_le_mul_of_nonneg_right _ h0
      exact_mod_cast (card_le_card (erase_subset _ _)).trans (card_powerset s).le

end WaveTurbulence.Induct
