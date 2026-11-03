/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure
public import WaveTurbulence.Foundations.WKEL2.Weight

/-!
# Orthogonality on resonant measure and weighted transfer
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Every pair in the measurable resonant chart is orthogonal. -/
theorem inner_resonantChart {e : Mom d} (he : ‖e‖ = 1)
    (p : Mom d × ↥(ℝ ∙ e)ᗮ) :
    ⟪(resonantChart e p).1, (resonantChart e p).2⟫_ℝ = 0 := by
  by_cases ha : p.1 = 0
  · simp only [resonantChart, ha, inner_zero_left]
  · change ⟪p.1, normalReflection e p.1 p.2⟫_ℝ = 0
    rw [← coe_hyperplaneChart he ha p.2]
    exact inner_eq_zero_of_mem_perp _

/-- Resonant measure is concentrated on orthogonal pairs. -/
theorem ae_inner_eq_zero {e : Mom d} (he : ‖e‖ = 1) :
    ∀ᵐ p ∂resonantMeasure e, ⟪p.1, p.2⟫_ℝ = 0 := by
  have hset : MeasurableSet {p : Mom d × Mom d | ⟪p.1, p.2⟫_ℝ = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  unfold resonantMeasure
  apply (ae_map_iff (measurable_resonantChart e).aemeasurable hset).mpr
  exact Filter.Eventually.of_forall (inner_resonantChart he)

end WaveTurbulence.WKEL2
