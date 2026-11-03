/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PositiveRayDensity
public import WaveTurbulence.Foundations.WKEL2.RadialEnergy

/-!
# Positive-ray samples in the spherical representation
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The absolute input times the extended positive radial density. -/
@[expose] def raySample (h : Mom d → ℝ) (k θ : Mom d) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |h (k + t • θ)| * positiveRayDensity (d - 2) t

theorem measurable_raySample {h : Mom d → ℝ} (hh : Measurable h) (k θ : Mom d) :
    Measurable (raySample h k θ) :=
  (hh.abs.ennreal_ofReal.comp (by fun_prop)).mul (measurable_positiveRayDensity _)

/-- Full-line integration of a positive-ray sample is the absolute ray mass. -/
theorem lintegral_raySample {h : Mom d → ℝ} (hh : Measurable h) (k θ : Mom d) :
    (∫⁻ t : ℝ, raySample h k θ t) = radialMass h k θ := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal |h (k + t • θ)|) :=
    hh.abs.ennreal_ofReal.comp (by fun_prop)
  simp only [raySample, mul_comm (ENNReal.ofReal _) (positiveRayDensity _ _)]
  exact lintegral_positiveRayDensity _ hm

end WaveTurbulence.WKEL2
