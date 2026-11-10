/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SphereMeasureIsometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Single directions have zero spherical measure in dimension at least two
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise ENNReal

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Directions in a proper linear subspace have zero surface measure. -/
theorem toSphere_submodule_null (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Submodule ℝ E) (hS : S ≠ ⊤) :
    μ.toSphere {x : sphere (0 : E) 1 | (x : E) ∈ S} = 0 := by
  have hm : MeasurableSet {x : sphere (0 : E) 1 | (x : E) ∈ S} :=
    S.closed_of_finiteDimensional.measurableSet.preimage measurable_subtype_coe
  have hsub : Ioo (0 : ℝ) 1 • (Subtype.val '' {x : sphere (0 : E) 1 | (x : E) ∈ S}) ⊆
      (S : Set E) := by
    rintro y ⟨r, hr, z, ⟨v, hv, rfl⟩, rfl⟩
    exact S.smul_mem r hv
  rw [μ.toSphere_apply' hm, measure_mono_null hsub (Measure.addHaar_submodule μ S hS), mul_zero]

end WaveTurbulence.WKEL2
