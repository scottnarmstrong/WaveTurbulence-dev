/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialEnergy
public import WaveTurbulence.Foundations.WKEL2.ResonantPolarOrder
public import WaveTurbulence.Foundations.WKEL2.AngularCoordinates

/-!
# Polar factorization of the second loss kernel
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The two radial integrations in the second loss term separate by Tonelli. -/
theorem lintegral_lossTwo_polar {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {f g : Mom d → ℝ} (hf : Measurable f) (hg : Measurable g) (k : Mom d) :
    (∫⁻ p, ENNReal.ofReal |f (k + p.1)| * ENNReal.ofReal |g (k + p.2)|
      ∂resonantMeasure e) =
      ∫⁻ p, radialMass f k p.1 * radialMass g k p.2 ∂angularMeasure e := by
  have hF : Measurable (fun p : Mom d × Mom d =>
      ENNReal.ofReal |f (k + p.1)| * ENNReal.ofReal |g (k + p.2)|) :=
    (hf.abs.ennreal_ofReal.comp (continuous_const.add continuous_fst).measurable).mul
      (hg.abs.ennreal_ofReal.comp (continuous_const.add continuous_snd).measurable)
  have hG : Measurable (fun p : Mom d × Mom d => radialMass f k p.1 * radialMass g k p.2) :=
    ((measurable_radialMass hf k).comp measurable_fst).mul
      ((measurable_radialMass hg k).comp measurable_snd)
  rw [lintegral_resonantMeasure_polar_angular_first he hd hF,
    lintegral_angularMeasure he hd hG]
  apply lintegral_congr
  intro φ
  apply lintegral_congr
  intro θ
  have hmr : Measurable (fun r : Ioi (0 : ℝ) =>
      ENNReal.ofReal |g (k + r.1 • normalReflection e φ.1 θ.1)|) :=
    hg.abs.ennreal_ofReal.comp (by fun_prop)
  simp_rw [lintegral_const_mul _ hmr]
  have hmf : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal |f (k + r.1 • φ.1)|) :=
    hf.abs.ennreal_ofReal.comp (by fun_prop)
  rw [lintegral_mul_const _ hmf]
  rfl

end WaveTurbulence.WKEL2
