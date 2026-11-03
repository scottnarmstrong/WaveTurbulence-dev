/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finiteness and equality of nonnegative Bochner integrals
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- A nonnegative measurable function with a specified finite lower integral
is integrable, and its Bochner integral has that value. -/
theorem integrable_integral_eq_of_lintegral_ofReal_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hm : AEStronglyMeasurable f μ) (hn : 0 ≤ᵐ[μ] f) {c : ℝ} (hc : 0 ≤ c)
    (he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal c) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = c := by
  have hf : HasFiniteIntegral f μ := by
    apply (hasFiniteIntegral_iff_ofReal hn).mpr
    rw [he]
    exact ENNReal.ofReal_lt_top
  refine ⟨⟨hm, hf⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm, he, ENNReal.toReal_ofReal hc]

end WaveTurbulence.WKEL2
