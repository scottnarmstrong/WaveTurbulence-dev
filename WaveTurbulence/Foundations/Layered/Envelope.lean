/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Measurable envelopes of continuous families

TARGET's norms `𝔛^{θ,Λ₁,Λ₂}` (L581) take the supremum over the momentum inside the frequency integral. If
the integrand is continuous in the momentum and measurable in the frequency, this envelope is measurable:

* `iSup_eq_iSup_dense_of_continuous`: a continuous `ℝ≥0∞`-valued function has the same supremum on a
  dense set;
* `measurable_iSup_of_continuous`: on a separable space, the supremum of a family continuous in the space
  variable and measurable in the parameter is measurable in the parameter.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Layered

theorem iSup_eq_iSup_dense_of_continuous {X : Type*} [TopologicalSpace X] {D : Set X}
    (hD : Dense D) {f : X → ℝ≥0∞} (hf : Continuous f) : ⨆ x, f x = ⨆ x : D, f x := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => le_iSup f x.1)
  have hc : IsClosed {y | f y ≤ ⨆ x : D, f x} := isClosed_le hf continuous_const
  have hsub : D ⊆ {y | f y ≤ ⨆ x : D, f x} := fun y hy => le_iSup (fun x : D => f x) ⟨y, hy⟩
  have := hc.closure_subset_iff.mpr hsub
  rw [hD.closure_eq] at this
  exact this (mem_univ x)

theorem measurable_iSup_of_continuous {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace Z] {g : Z → X → ℝ≥0∞}
    (hc : ∀ z, Continuous (g z)) (hm : ∀ x, Measurable fun z => g z x) :
    Measurable fun z => ⨆ x, g z x := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have h : (fun z => ⨆ x, g z x) = fun z => ⨆ x : D, g z x :=
    funext fun z => iSup_eq_iSup_dense_of_continuous hDd (hc z)
  rw [h]
  have := hDc.to_subtype
  exact Measurable.iSup fun x => hm x

end WaveTurbulence.Layered
