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

/-- Surface measure has no atoms when the ambient dimension is at least two. -/
theorem toSphere_noAtoms (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 2 ≤ Module.finrank ℝ E) : NullSingletonClass μ.toSphere := by
  constructor
  intro x
  have hx : (x : E) ≠ 0 := by
    intro h
    have hx1 := mem_sphere_zero_iff_norm.mp x.2
    simp only [h, norm_zero, zero_ne_one] at hx1
  have hproper : (ℝ ∙ (x : E)) ≠ ⊤ := by
    intro h
    have hr := finrank_span_singleton (K := ℝ) hx
    rw [h, finrank_top] at hr
    omega
  have hsub : Ioo (0 : ℝ) 1 • (Subtype.val '' ({x} : Set (sphere (0 : E) 1))) ⊆
      (ℝ ∙ (x : E) : Set E) := by
    rintro y ⟨r, hr, z, ⟨v, hv, rfl⟩, rfl⟩
    have hvx : v = x := mem_singleton_iff.mp hv
    subst v
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  rw [μ.toSphere_apply' (measurableSet_singleton x),
    measure_mono_null hsub (Measure.addHaar_submodule μ _ hproper), mul_zero]

end WaveTurbulence.WKEL2
