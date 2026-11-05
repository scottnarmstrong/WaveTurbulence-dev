/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Dropping the time ordering (S3b LADDER-DECAY)

A finite sum of integrals over an ordered time region is bounded by the integral over any
larger region of the modulus of the (finite) integrand sum. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open MeasureTheory Finset

variable {X ι : Type*} [MeasurableSpace X]

theorem norm_sum_integral_indicator_le (μ : Measure X) (s : Finset ι) (F : ι → ℂ)
    (g : ι → X → ℂ) (C B : Set X) (hC : MeasurableSet C) (hCB : C ⊆ B)
    (hint : ∀ z ∈ s, Integrable (C.indicator (g z)) μ)
    (hB : IntegrableOn (fun x => ‖∑ z ∈ s, F z * g z x‖) B μ) :
    ‖∑ z ∈ s, F z * ∫ x, C.indicator (g z) x ∂μ‖ ≤ ∫ x in B, ‖∑ z ∈ s, F z * g z x‖ ∂μ := by
  have h1 : ∑ z ∈ s, F z * ∫ x, C.indicator (g z) x ∂μ =
      ∫ x, C.indicator (fun x => ∑ z ∈ s, F z * g z x) x ∂μ := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun z hz => (hint z hz).const_mul (F z))]
    congr 1
    funext x
    by_cases hx : x ∈ C
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [h1]
  calc ‖∫ x, C.indicator (fun x => ∑ z ∈ s, F z * g z x) x ∂μ‖
      ≤ ∫ x, ‖C.indicator (fun x => ∑ z ∈ s, F z * g z x) x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x in C, ‖∑ z ∈ s, F z * g z x‖ ∂μ := by
        rw [← integral_indicator hC]
        congr 1
        funext x
        by_cases hx : x ∈ C <;> simp [hx]
    _ ≤ ∫ x in B, ‖∑ z ∈ s, F z * g z x‖ ∂μ :=
        setIntegral_mono_set hB (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (Filter.Eventually.of_forall hCB)

end WaveTurbulence.LadderDecay
