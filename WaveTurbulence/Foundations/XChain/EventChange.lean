/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cumulant.Basic
public import WaveTurbulence.Foundations.Probability.RestrictedCauchySchwarz
public import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! TARGET S7, L816: exact event-change expansion; every term contains a removed-event moment. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

/-- Removing the empty-subset term from the product expansion leaves only error-bearing terms. -/
theorem prod_sub_error_terms {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f g : ι → R) :
    (∏ i ∈ s, (f i - g i)) - ∏ i ∈ s, f i =
      ∑ t ∈ s.powerset.erase ∅, (-1) ^ t.card * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i := by
  classical
  rw [Finset.prod_sub]
  have he := Finset.sum_erase_add (s := s.powerset) (a := ∅)
    (fun t => (-1 : R) ^ t.card * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i)
    (Finset.empty_mem_powerset s)
  rw [← he]
  simp

/-- S7 as an exact finite expression, for the literal unnormalized cumulant.
Each selected nonempty set of partition blocks contributes moments on A\\B. -/
theorem cumulant_event_change {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {A B : Set Ω}
    (hB : MeasurableSet B) (hBA : B ⊆ A)
    (hi : ∀ J ⊆ s, IntegrableOn (fun ω => ∏ j ∈ J, X j ω) A μ) :
    cumulant (μ.restrict B) X s - cumulant (μ.restrict A) X s =
      ∑ P : Finpartition s,
        (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
        ∑ T ∈ P.parts.powerset.erase ∅, (-1 : ℂ) ^ T.card *
          (∏ J ∈ P.parts \ T, ∫ ω in A, ∏ j ∈ J, X j ω ∂μ) *
          ∏ J ∈ T, ∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ := by
  classical
  unfold cumulant
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [← mul_sub]
  congr 1
  have he (J : Finset ι) (hJ : J ∈ P.parts) :
      (∫ ω in B, ∏ j ∈ J, X j ω ∂μ) =
        (∫ ω in A, ∏ j ∈ J, X j ω ∂μ) - ∫ ω in A \ B, ∏ j ∈ J, X j ω ∂μ := by
    rw [setIntegral_sdiff hB (hi J (P.le hJ)) hBA, sub_sub_cancel]
  rw [Finset.prod_congr rfl he]
  exact prod_sub_error_terms P.parts _ _

/-- The removed-event moment gains the square-root event probability, with expectation
still under the old event A. This is the Cauchy–Schwarz factor used in S7. -/
theorem event_change_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B : Set Ω} (hB : MeasurableSet B)
    {f : Ω → ℂ} (hf : MemLp f 2 (μ.restrict A)) :
    ‖∫ ω in A \ B, f ω ∂μ‖ ≤ Real.sqrt (μ.real (A \ B)) *
      Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) := by
  have h := Probability.norm_setIntegral_le_sqrt_measure_mul hf Bᶜ
  have he : Bᶜ ∩ A = A \ B := by
    ext ω
    exact and_comm
  rw [Measure.restrict_restrict hB.compl, he,
    measureReal_restrict_apply hB.compl, he] at h
  exact h

end WaveTurbulence.Induct
