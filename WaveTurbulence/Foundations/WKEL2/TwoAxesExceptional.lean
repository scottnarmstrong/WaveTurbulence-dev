/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.TwoAxes

/-!
# The null exceptional directions in the two-axis slicing formula
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- For a fixed nonzero first axis, the degenerate second directions form a null set. -/
theorem ae_transverseAxis_ne_zero (hd : 2 ≤ d) {θ : Mom d} (hθ : θ ≠ 0) :
    ∀ᵐ v : sphere (0 : Mom d) 1 ∂(volume : Measure (Mom d)).toSphere,
      transverseAxis hθ v.1 ≠ 0 := by
  have hproper : (ℝ ∙ θ) ≠ ⊤ := by
    intro h
    have hr := finrank_span_singleton (K := ℝ) hθ
    rw [h, finrank_top, finrank_euclideanSpace_fin] at hr
    omega
  have hsub : {v : sphere (0 : Mom d) 1 | transverseAxis hθ v.1 = 0} ⊆
      {v : sphere (0 : Mom d) 1 | (v : Mom d) ∈ (ℝ ∙ θ)} := by
    intro v hv
    have hp : perpPart θ (v : Mom d) = 0 := by
      apply (perpIsometry hθ).injective
      change perpIsometry hθ (perpPart θ (v : Mom d)) = 0 at hv
      simpa only [map_zero] using hv
    have heq := eq_smul_add_perpPart θ (v : Mom d)
    rw [hp, Submodule.coe_zero, add_zero] at heq
    change (v : Mom d) ∈ (ℝ ∙ θ)
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self θ))
  have hnull := measure_mono_null hsub
    (toSphere_submodule_null (volume : Measure (Mom d)) (ℝ ∙ θ) hproper)
  apply ae_iff.mpr
  simpa only [not_not] using hnull

end WaveTurbulence.WKEL2
