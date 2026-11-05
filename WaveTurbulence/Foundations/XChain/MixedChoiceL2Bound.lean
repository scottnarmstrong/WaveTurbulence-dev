/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MixedProductL2Bound
/-! Mixed choices retain a small remainder factor after conditional integration. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset Set

theorem norm_mixed_choice_le_of_L2 {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A) (X Y : ι → Ω → ℂ)
    (s : Finset ι) (f : ι → Bool) {i : ι} (hi : i ∈ s) (hfi : f i = true)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmem : ∀ J ⊆ s, MemLp (fun ω => ∏ j ∈ J, X j ω) 2 (μ.restrict A))
    (h2 : ∀ J ⊆ s, (∫ ω in A, ‖∏ j ∈ J, X j ω‖ ^ 2 ∂μ) ≤
      (((C * J.card).factorial : ℝ) * ∏ j ∈ J, M j) ^ 2)
    (hb : ∀ᵐ ω ∂μ.restrict B, ∀ j ∈ s, ‖Y j ω‖ ≤ ε * M j) :
    ‖∫ ω in B, ∏ j ∈ s, (if f j then Y j ω else X j ω) ∂μ‖ ≤
      ε * ((C * s.card).factorial : ℝ) * ∏ j ∈ s, M j := by
  classical
  let K := s.filter (fun j => f j = true)
  have hK : K ⊆ s := filter_subset _ _
  have he (ω : Ω) : (∏ j ∈ K, Y j ω) * (∏ j ∈ s \ K, X j ω) =
      ∏ j ∈ s, (if f j then Y j ω else X j ω) := by
    have hdiff : s \ K = s.filter (fun j => ¬ f j = true) := by
      ext j
      simp [K]
      tauto
    rw [hdiff]
    have h := prod_filter_mul_prod_filter_not s (fun j => f j = true)
      (fun j => if f j then Y j ω else X j ω)
    apply Eq.trans ?_ h
    apply congrArg₂ (· * ·)
    · apply prod_congr rfl
      intro j hj
      have ht : f j = true := (mem_filter.mp hj).2
      simp [ht]
    · apply prod_congr rfl
      intro j hj
      have ht : ¬ f j = true := (mem_filter.mp hj).2
      simp [ht]
  simp_rw [← he]
  apply norm_mixed_product_le_of_L2 hB hBA X Y s K hK
    ⟨i, by simp [K, hi, hfi]⟩ C M hM hε hε1
    (hmem _ Finset.sdiff_subset) (h2 _ Finset.sdiff_subset)
  exact hb.mono fun ω hω j hj => hω j (hK hj)

end WaveTurbulence.Induct
