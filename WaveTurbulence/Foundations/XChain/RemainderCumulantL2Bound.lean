/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MixedChoiceL2Bound
public import WaveTurbulence.Foundations.XChain.CumulantRemainderBound
/-! S6 directly from old-event L2 moments and pointwise fixedpoint remainder bounds. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset Set
open scoped ENNReal

theorem norm_cumulant_add_error_le_of_L2 {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A) (X Y : ι → Ω → ℂ)
    (hX : ∀ i, ∀ q : ℕ, 1 ≤ q → MemLp (X i) (q : ℝ≥0∞) (μ.restrict B))
    (hY : ∀ i, ∀ q : ℕ, 1 ≤ q → MemLp (Y i) (q : ℝ≥0∞) (μ.restrict B))
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmem : ∀ J : Finset ι, MemLp (fun ω => ∏ j ∈ J, X j ω) 2 (μ.restrict A))
    (h2 : ∀ J : Finset ι, (∫ ω in A, ‖∏ j ∈ J, X j ω‖ ^ 2 ∂μ) ≤
      (((C * J.card).factorial : ℝ) * ∏ j ∈ J, M j) ^ 2)
    (hb : ∀ᵐ ω ∂μ.restrict B, ∀ j, ‖Y j ω‖ ≤ ε * M j) :
    ‖cumulant (μ.restrict B) (fun j ω => X j ω + Y j ω) univ -
        cumulant (μ.restrict B) X univ‖ ≤
      ε * 2 ^ Fintype.card ι * ((C + 2) * Fintype.card ι).factorial * ∏ j, M j := by
  have hs (f : ι → Bool) (J : Finset ι) (i : ι) (hi : i ∈ J) (hfi : f i = true) :
      ‖∫ ω in B, ∏ j ∈ J, (if f j then Y j ω else X j ω) ∂μ‖ ≤
        ε * ((C * J.card).factorial : ℝ) * ∏ j ∈ J, M j :=
    norm_mixed_choice_le_of_L2 hB hBA X Y J f hi hfi C M hM hε hε1
      (fun K _ => hmem K) (fun K _ => h2 K) (hb.mono fun ω hω j _ => hω j)
  apply norm_cumulant_add_error_le (μ.restrict B) X Y hX hY C M hM hε
  · intro f J _
    by_cases h : ∃ i ∈ J, f i = true
    · obtain ⟨i, hi, hfi⟩ := h
      exact (hs f J i hi hfi).trans (by
        simpa only [mul_assoc] using mul_le_of_le_one_left
          (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)) hε1)
    · have he (ω : Ω) : (∏ j ∈ J, (if f j then Y j ω else X j ω)) = ∏ j ∈ J, X j ω := by
        apply prod_congr rfl
        intro j hj
        have hjf : f j ≠ true := fun hh => h ⟨j, hj, hh⟩
        simp [hjf]
      simp_rw [he]
      have hf := (hmem J).mono_measure (Measure.restrict_mono hBA le_rfl)
      have hn := norm_setIntegral_mul_le_of_bound hB hBA (hmem J) zero_le_one
        (Filter.Eventually.of_forall (fun _ => (norm_one (α := ℂ)).le))
      simp only [one_mul] at hn
      exact hn.trans ((Real.sqrt_le_sqrt (h2 J)).trans_eq
        (Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j))))
  · intro f i hfi J hi
    simpa only [mul_assoc] using hs f J i hi hfi

end WaveTurbulence.Induct
