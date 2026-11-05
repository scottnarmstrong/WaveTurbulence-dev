/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChange
/-! Quantitative finite-partition control of S7 event-change errors, TARGET L816. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

/-- A product with one small factor retains that factor, without dividing by weights. -/
theorem prod_le_small_factor {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f M : ι → ℝ) {i : ι} (hi : i ∈ s) {ε : ℝ}
    (h0 : ∀ j ∈ s, 0 ≤ f j)
    (hbound : ∀ j ∈ s, f j ≤ M j) (hsmall : f i ≤ ε * M i) :
    ∏ j ∈ s, f j ≤ ε * ∏ j ∈ s, M j := by
  have hb : ∀ j ∈ s, f j ≤ (if j = i then ε else 1) * M j := by
    intro j hj
    by_cases hji : j = i
    · simpa only [hji, ite_true] using hsmall
    · simpa only [hji, ite_false, one_mul] using hbound j hj
  calc
    _ ≤ ∏ j ∈ s, (if j = i then ε else 1) * M j := Finset.prod_le_prod₀ h0 hb
    _ = (∏ j ∈ s, if j = i then ε else 1) * ∏ j ∈ s, M j := Finset.prod_mul_distrib
    _ = _ := by simp [hi]

/-- An error-bearing partition term gains one epsilon even if several blocks are errors. -/
theorem error_block_product_bound {ι : Type*} [DecidableEq ι] (s T : Finset ι)
    (hT : T ⊆ s) (hne : T.Nonempty) (f g : ι → ℂ) (M : ι → ℝ) {ε : ℝ}
    (hε1 : ε ≤ 1) (hM : ∀ j ∈ s, 0 ≤ M j)
    (hf : ∀ j ∈ s, ‖f j‖ ≤ M j) (hg : ∀ j ∈ s, ‖g j‖ ≤ ε * M j) :
    ‖(∏ j ∈ s \ T, f j) * ∏ j ∈ T, g j‖ ≤ ε * ∏ j ∈ s, M j := by
  classical
  obtain ⟨i, hi⟩ := hne
  let v := fun j => if j ∈ T then ‖g j‖ else ‖f j‖
  have hnot : s.filter (fun j => j ∉ T) = s \ T := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff]
  have he : (∏ j ∈ s, v j) = ‖(∏ j ∈ s \ T, f j) * ∏ j ∈ T, g j‖ := by
    dsimp only [v]
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter,
      hnot, Finset.inter_eq_right.mpr hT, norm_mul, norm_prod, norm_prod,
      mul_comm]
  rw [← he]
  apply prod_le_small_factor s v M (hT hi)
  · intro j _
    dsimp only [v]
    split_ifs <;> exact norm_nonneg _
  · intro j hj
    dsimp only [v]
    split_ifs
    · exact (hg j hj).trans (mul_le_of_le_one_left (hM j hj) hε1)
    · exact hf j hj
  · simpa only [v, ite_eq_left hi] using hg i (hT hi)

end WaveTurbulence.Induct
