/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure
public import WaveTurbulence.Foundations.WKE.DeltaReading

/-!
# Bochner integration against resonant measure

The resonant measure omits the collision operator's factor one half.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Signed integration against resonant measure in fixed coordinates. -/
theorem integral_resonantMeasure_chart (e : Mom d) {F : Mom d × Mom d → ℝ}
    (hF : Integrable F (resonantMeasure e)) :
    ∫ p, F p ∂resonantMeasure e =
      ∫ a : Mom d, ‖a‖⁻¹ * ∫ w : ↥(ℝ ∙ e)ᗮ, F (a, normalReflection e a w) := by
  let ρ := fun p : Mom d × ↥(ℝ ∙ e)ᗮ => ENNReal.ofReal (‖p.1‖⁻¹)
  have hρ : Measurable ρ := (measurable_norm.comp measurable_fst).inv.ennreal_ofReal
  have hρfin : ∀ᵐ p ∂(volume.prod volume), ρ p < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hm := measurable_resonantChart e
  have hi : Integrable (fun p => F (resonantChart e p))
      ((volume.prod volume).withDensity ρ) :=
    hF.comp_measurable hm
  have hi' := (integrable_withDensity_iff_integrable_smul' hρ hρfin).mp hi
  have heq : (fun p : Mom d × ↥(ℝ ∙ e)ᗮ => (ρ p).toReal • F (resonantChart e p)) =
      (fun p => ‖p.1‖⁻¹ * F (resonantChart e p)) := by
    funext p
    rw [smul_eq_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))]
  rw [heq] at hi'
  rw [resonantMeasure, integral_map hm.aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hρ hρfin, heq,
    integral_prod _ hi']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    dsimp only [resonantChart]
    exact integral_const_mul (‖a‖⁻¹) (fun w : ↥(ℝ ∙ e)ᗮ => F (a, normalReflection e a w))

/-- Signed intrinsic hyperplane formula, with the factor two relative to `deltaInt`. -/
theorem integral_resonantMeasure_eq_two_deltaInt {e : Mom d} (he : ‖e‖ = 1)
    {F : Mom d × Mom d → ℝ} (hF : Integrable F (resonantMeasure e)) :
    ∫ p, F p ∂resonantMeasure e = 2 * deltaInt (fun a b => F (a, b)) := by
  rw [integral_resonantMeasure_chart e hF, deltaInt, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    dsimp only
    by_cases ha : a = 0
    · subst a
      simp only [norm_zero, inv_zero, mul_zero, zero_mul]
    · have hchart := (measurePreserving_hyperplaneChart he ha).integral_comp'
        (f := (hyperplaneChart he ha).toMeasurableEquiv) (fun w => F (a, w))
      simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, coe_hyperplaneChart] at hchart
      rw [hchart, mul_inv]
      ring

end WaveTurbulence.WKEL2
