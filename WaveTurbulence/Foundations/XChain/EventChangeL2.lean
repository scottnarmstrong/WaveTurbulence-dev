/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeWeighted
/-! S7 Cauchy–Schwarz applied to the complete weighted cumulant expansion. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

/-- One L2 moment bound controls both the old moment and the removed-event moment. -/
theorem moment_event_bounds_of_L2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hB : MeasurableSet B)
    {f : Ω → ℂ} (hf : MemLp f 2 (μ.restrict A)) {M : ℝ} (hM : 0 ≤ M)
    (h2 : (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) ≤ M ^ 2) :
    ‖∫ ω in A, f ω ∂μ‖ ≤ M ∧
      ‖∫ ω in A \ B, f ω ∂μ‖ ≤ Real.sqrt (μ.real (A \ B)) * M := by
  have hs : Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) ≤ M := by
    exact (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq hM)
  have hp : Real.sqrt (μ.real A) ≤ 1 :=
    (Real.sqrt_le_sqrt (measureReal_le_one (μ := μ) (s := A))).trans_eq Real.sqrt_one
  constructor
  · have h := event_change_moment_bound (A := A) MeasurableSet.empty hf
    simp only [Set.sdiff_empty] at h
    exact h.trans (by simpa only [one_mul] using
      (mul_le_mul hp hs (Real.sqrt_nonneg _) zero_le_one))
  · exact (event_change_moment_bound hB hf).trans
      (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _))

/-- The source S7 estimate: full cumulant difference gains the square root of the deleted
probability, retaining every individual momentum weight and explicit factorial losses. -/
theorem norm_cumulant_event_change_le_of_L2 {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℂ) (s : Finset ι)
    {A B : Set Ω} (hB : MeasurableSet B) (hBA : B ⊆ A)
    (C : ℕ) (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hmem : ∀ J ⊆ s, MemLp (fun ω => ∏ j ∈ J, X j ω) 2 (μ.restrict A))
    (h2 : ∀ J ⊆ s, J.Nonempty →
      (∫ ω in A, ‖∏ j ∈ J, X j ω‖ ^ 2 ∂μ) ≤
        (((C * J.card).factorial : ℝ) * ∏ j ∈ J, M j) ^ 2) :
    ‖cumulant (μ.restrict B) X s - cumulant (μ.restrict A) X s‖ ≤
      Real.sqrt (μ.real (A \ B)) * 2 ^ s.card * ((C + 2) * s.card).factorial *
        ∏ j ∈ s, M j := by
  have hp : Real.sqrt (μ.real (A \ B)) ≤ 1 :=
    (Real.sqrt_le_sqrt (measureReal_le_one (μ := μ))).trans_eq Real.sqrt_one
  apply norm_cumulant_event_change_weighted_le μ X s hB hBA
    (fun J hJ => (hmem J hJ).integrable (by norm_num)) C M hM (Real.sqrt_nonneg _) hp
  · intro J hJ hne
    exact (moment_event_bounds_of_L2 hB (hmem J hJ)
      (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)) (h2 J hJ hne)).1
  · intro J hJ hne
    exact (moment_event_bounds_of_L2 hB (hmem J hJ)
      (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun j _ => hM j)) (h2 J hJ hne)).2

end WaveTurbulence.Induct
