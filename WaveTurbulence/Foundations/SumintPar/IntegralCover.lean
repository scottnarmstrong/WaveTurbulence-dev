/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Integral bounds under overlapping domain covers

The small and large time regions meet at their common endpoint. A
nonnegative integral over their union is bounded by their sum without
requiring an artificial disjointness convention.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- A measurable two-set cover bounds every nonnegative integrable function. -/
theorem integral_union_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    (∫ x in s ∪ t, f x ∂μ) ≤ (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  have hiS := hfs.integrable_indicator hs
  have hiT := hft.integrable_indicator ht
  rw [← integral_indicator (hs.union ht), ← integral_indicator hs,
    ← integral_indicator ht, ← integral_add hiS hiT]
  apply integral_mono ((hfs.union hft).integrable_indicator (hs.union ht)) (hiS.add hiT)
  intro x
  by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;>
    simp [hx, hy, le_add_iff_nonneg_right, hf x]

end WaveTurbulence.SumintPar
