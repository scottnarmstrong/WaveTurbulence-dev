/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure
public import WaveTurbulence.Foundations.WKEL2.HyperplaneScaling
public import WaveTurbulence.Foundations.WKEL2.PolarRadial

/-!
# Polar coordinates for resonant measure

Corollary 2 of `docs/research/git20-general-d.md`, expressed in a fixed
reference hyperplane so that every integral has an explicit measurable domain.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Polar coordinates in the first normal, with the inverse norm lowering
its radial exponent from `d-1` to `d-2`. -/
theorem lintegral_resonantMeasure_polar_left (e : Mom d) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂resonantMeasure e =
      ∫⁻ θ : sphere (0 : Mom d) 1, ∫⁻ r : Ioi (0 : ℝ),
        (∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (r.1 • θ.1, normalReflection e θ.1 w))
        ∂Measure.volumeIoiPow (d - 2) ∂(volume : Measure (Mom d)).toSphere := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (show 0 < d by omega))
  have hm : Measurable (fun a : Mom d =>
      ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w)) :=
    (hF.comp (measurable_resonantChart e)).lintegral_prod_right'
  have hH : Measurable (fun a : Mom d => ENNReal.ofReal (‖a‖⁻¹) *
      ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w)) :=
    measurable_norm.inv.ennreal_ofReal.mul hm
  rw [lintegral_resonantMeasure_chart e hF, lintegral_polar volume hH]
  apply lintegral_congr
  intro θ
  have hθ : ‖(θ : Mom d)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using θ.2
  have hr : (fun r : Ioi (0 : ℝ) =>
      ENNReal.ofReal (‖r.1 • θ.1‖⁻¹) *
        ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (r.1 • θ.1, normalReflection e (r.1 • θ.1) w)) =
      (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹) *
        ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (r.1 • θ.1, normalReflection e θ.1 w)) := by
    funext r
    rw [normalReflection_pos_smul e θ.1 r.2, norm_smul, Real.norm_of_nonneg r.2.le,
      hθ, mul_one]
  rw [finrank_euclideanSpace_fin, hr]
  have hG : Measurable (fun r : Ioi (0 : ℝ) =>
      ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (r.1 • θ.1, normalReflection e θ.1 w)) := by
    have hc : Continuous (fun p : Ioi (0 : ℝ) × ↥(ℝ ∙ e)ᗮ =>
        (p.1.1 • θ.1, normalReflection e θ.1 p.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk
        ((normalReflection e θ.1).continuous.comp
          (continuous_subtype_val.comp continuous_snd))
    exact (hF.comp hc.measurable).lintegral_prod_right'
  simpa only [show d - 2 + 1 = d - 1 by omega] using
    (lintegral_volumeIoiPow_inv (d - 2) hG)

end WaveTurbulence.WKEL2
