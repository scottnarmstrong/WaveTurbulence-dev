/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PolarDensity

/-!
# The positive-ray radial density on the whole real line
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Extending the positive radial density by zero avoids endpoint conventions. -/
@[expose] def positiveRayDensity (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ n))

theorem measurable_positiveRayDensity (n : ℕ) : Measurable (positiveRayDensity n) :=
  (measurable_id.pow_const n).ennreal_ofReal.indicator measurableSet_Ioi

/-- Full-line expression for the weighted positive-ray integral. -/
theorem lintegral_positiveRayDensity (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ t : ℝ, positiveRayDensity n t * F t) =
      ∫⁻ r : Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow n := by
  rw [lintegral_volumeIoiPow_comp n hF, positiveRayDensity, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  exact (Set.indicator_mul_left (Ioi (0 : ℝ)) (fun r => ENNReal.ofReal (r ^ n)) F).symm


end WaveTurbulence.WKEL2
