/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantPolarFull

/-!
# Angular-first order of resonant polar integration

The order of integration in Corollary 2 of the general-dimensional research note.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Corollary 2, with both angular variables preceding both radii. -/
theorem lintegral_resonantMeasure_polar_angular_first {e : Mom d} (he : ‖e‖ = 1)
    (hd : 2 ≤ d) {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂resonantMeasure e =
      ∫⁻ φ : sphere (0 : Mom d) 1,
        ∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1,
          ∫⁻ ρ : Ioi (0 : ℝ), ∫⁻ r : Ioi (0 : ℝ),
            F (ρ.1 • φ.1, r.1 • normalReflection e φ.1 θ.1)
              ∂Measure.volumeIoiPow (d - 2) ∂Measure.volumeIoiPow (d - 2)
            ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
          ∂(volume : Measure (Mom d)).toSphere := by
  rw [lintegral_resonantMeasure_polar he hd hF]
  apply lintegral_congr
  intro φ
  have hH : Continuous (normalReflection e φ.1) := (normalReflection e φ.1).continuous
  have hc : Continuous (fun q :
      (Ioi (0 : ℝ) × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1) × Ioi (0 : ℝ) =>
      (q.1.1.1 • φ.1, q.2.1 • normalReflection e φ.1 q.1.2.1)) := by
    fun_prop
  have hI : Measurable (fun p : Ioi (0 : ℝ) × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1 =>
      ∫⁻ r : Ioi (0 : ℝ), F (p.1.1 • φ.1, r.1 • normalReflection e φ.1 p.2.1)
        ∂Measure.volumeIoiPow (d - 2)) :=
    (hF.comp hc.measurable).lintegral_prod_right'
  exact lintegral_lintegral_swap hI.aemeasurable

end WaveTurbulence.WKEL2
