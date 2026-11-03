/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularCoordinates

/-!
# Angular integration as an ordinary product integral
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The fixed-sphere angular coordinates as a measurable map. -/
@[expose] def angularPair (e : Mom d)
    (p : sphere (0 : Mom d) 1 × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1) : Mom d × Mom d :=
  (p.1.1, normalReflection e p.1.1 p.2.1)

/-- Both coordinates of the angular map are unit vectors. -/
theorem angularPair_norms (e : Mom d)
    (p : sphere (0 : Mom d) 1 × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1) :
    ‖(angularPair e p).1‖ = 1 ∧ ‖(angularPair e p).2‖ = 1 := by
  constructor
  · exact mem_sphere_zero_iff_norm.mp p.1.2
  · change ‖normalReflection e p.1.1 (p.2.1 : Mom d)‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact mem_sphere_zero_iff_norm.mp p.2.2

/-- Angular integrals can be computed on the product of two fixed spheres. -/
theorem lintegral_angularProduct {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {G : Mom d × Mom d → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G (angularPair e p)
      ∂((volume : Measure (Mom d)).toSphere.prod
        (volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere)) = ∫⁻ p, G p ∂angularMeasure e := by
  unfold angularPair
  rw [lintegral_prod _ (measurable_angularIntegrand e hG).aemeasurable,
    lintegral_angularMeasure he hd hG]

end WaveTurbulence.WKEL2
