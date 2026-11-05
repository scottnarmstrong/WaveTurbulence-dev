/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MixedMomentBound
public import WaveTurbulence.Foundations.XChain.EventChangeBounds
/-! A pointwise small product and an old-event L2 moment control each S6 mixed moment. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset Set

theorem norm_mixed_product_le_of_L2 {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A) (X Y : ι → Ω → ℂ)
    (s K : Finset ι) (hK : K ⊆ s) (hne : K.Nonempty)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hf : MemLp (fun ω => ∏ j ∈ s \ K, X j ω) 2 (μ.restrict A))
    (h2 : (∫ ω in A, ‖∏ j ∈ s \ K, X j ω‖ ^ 2 ∂μ) ≤
      (((C * (s \ K).card).factorial : ℝ) * ∏ j ∈ s \ K, M j) ^ 2)
    (hb : ∀ᵐ ω ∂μ.restrict B, ∀ j ∈ K, ‖Y j ω‖ ≤ ε * M j) :
    ‖∫ ω in B, (∏ j ∈ K, Y j ω) * (∏ j ∈ s \ K, X j ω) ∂μ‖ ≤
      ε * ((C * s.card).factorial : ℝ) * ∏ j ∈ s, M j := by
  have hprod : ∀ᵐ ω ∂μ.restrict B, ‖∏ j ∈ K, Y j ω‖ ≤ ε * ∏ j ∈ K, M j := by
    filter_upwards [hb] with ω hω
    obtain ⟨i, hi⟩ := hne
    rw [norm_prod]
    exact prod_le_small_factor K (fun j => ‖Y j ω‖) M hi
      (fun _ _ => norm_nonneg _) (fun j hj => (hω j hj).trans
        (mul_le_of_le_one_left (hM j) hε1)) (hω i hi)
  have hsqrt : Real.sqrt (∫ ω in A, ‖∏ j ∈ s \ K, X j ω‖ ^ 2 ∂μ) ≤
      ((C * (s \ K).card).factorial : ℝ) * ∏ j ∈ s \ K, M j :=
    (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq
      (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)))
  have h := norm_setIntegral_mul_le_of_bound hB hBA hf
    (mul_nonneg hε (prod_nonneg fun j _ => hM j)) hprod
  have hfac : ((C * (s \ K).card).factorial : ℝ) ≤ ((C * s.card).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.mul_le_mul_left C (Finset.card_le_card Finset.sdiff_subset))
  calc
    _ ≤ (ε * ∏ j ∈ K, M j) *
        (((C * (s \ K).card).factorial : ℝ) * ∏ j ∈ s \ K, M j) :=
      h.trans (mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hε (prod_nonneg fun j _ => hM j)))
    _ = ε * ((C * (s \ K).card).factorial : ℝ) * ∏ j ∈ s, M j := by
      rw [← prod_sdiff hK]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hε)
      (prod_nonneg fun j _ => hM j)

end WaveTurbulence.Induct
