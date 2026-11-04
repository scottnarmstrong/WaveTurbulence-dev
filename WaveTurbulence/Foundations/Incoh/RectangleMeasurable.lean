/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RectangleIndicator

/-!
# Measurable rectangular time fibers

The endpoints may be measurable functions of all remaining clocks.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The literal rectangular indicator is measurable jointly in endpoints and clocks. -/
theorem measurable_rectangleIndicator_comp {Z : Type*} [MeasurableSpace Z]
    {a b t : Z → Fin 2 → ℝ} (ha : Measurable a) (hb : Measurable b) (ht : Measurable t) :
    Measurable (fun z => rectangleIndicator (a z) (b z) (t z)) := by
  have hj (j : Fin 2) : Measurable (fun z =>
      (Ioc (a z j) (b z j)).indicator (fun _ => (1 : ℝ)) (t z j)) := by
    have hs : MeasurableSet {z | a z j < t z j ∧ t z j ≤ b z j} :=
      (measurableSet_lt ((measurable_pi_apply j).comp ha) ((measurable_pi_apply j).comp ht)).inter
        (measurableSet_le ((measurable_pi_apply j).comp ht) ((measurable_pi_apply j).comp hb))
    exact Measurable.ite hs measurable_const measurable_const
  exact (Complex.continuous_ofReal.measurable.comp (hj 0)).mul
    (Complex.continuous_ofReal.measurable.comp (hj 1))

end WaveTurbulence.Incoh
