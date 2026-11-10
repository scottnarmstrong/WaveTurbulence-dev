/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularMeasure
public import WaveTurbulence.Foundations.WKEL2.RadialCutoff

/-!
# The angular measure in fixed sphere coordinates

Identify the normalized radial-cutoff measure with the two sphere integrals
in research-note Corollary 2.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The normalized direction of a unit vector is that vector. -/
theorem unitVec_of_norm_one {x : Mom d} (hx : ‖x‖ = 1) : unitVec x = x := by
  rw [unitVec, hx, inv_one, one_smul]

/-- The radial cutoff and the direction map in polar coordinates. -/
theorem cutoff_pairDirections_smul {x y : Mom d} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (G : Mom d × Mom d → ℝ≥0∞) :
    (ball (0 : Mom d × Mom d) 1).indicator (fun p => G (pairDirections p)) (ρ • x, r • y) =
      if ρ < 1 ∧ r < 1 then G (x, y) else 0 := by
  simp only [Set.indicator, mem_ball_zero_iff, Prod.norm_def, norm_smul,
    Real.norm_of_nonneg hρ.le, Real.norm_of_nonneg hr.le, hx, hy, mul_one,
    max_lt_iff, pairDirections, unitVec_pos_smul x hρ, unitVec_pos_smul y hr,
    unitVec_of_norm_one hx, unitVec_of_norm_one hy]

/-- Joint measurability of the angular integrand on the two fixed spheres. -/
theorem measurable_angularIntegrand (e : Mom d) {G : Mom d × Mom d → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable (fun p : sphere (0 : Mom d) 1 × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1 =>
      G (p.1.1, normalReflection e p.1.1 p.2.1)) := by
  have hc : Measurable (fun p : sphere (0 : Mom d) 1 × sphere (0 : ↥(ℝ ∙ e)ᗮ) 1 =>
      (p.1.1, p.2.1)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).measurable
  exact (hG.comp (measurable_resonantChart e)).comp hc

/-- The normalization of both radial cutoffs is exactly one. -/
theorem angular_radial_normalization (hd : 2 ≤ d) :
    ENNReal.ofReal (((d : ℝ) - 1) ^ 2) * (radialUnitMass (d - 2)) ^ 2 = 1 := by
  have hcast : ((d - 2 : ℕ) : ℝ) + 1 = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
    ring
  have hpos : 0 < (d : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [h]
  rw [radialUnitMass_eq, hcast, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  have hnum : ((d : ℝ) - 1) ^ 2 * (1 / ((d : ℝ) - 1)) ^ 2 = 1 := by
    field_simp [hpos.ne']
  rw [hnum, ENNReal.ofReal_one]

/-- Identification of angular resonant measure with the two sphere integrals. -/
theorem lintegral_angularMeasure {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {G : Mom d × Mom d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ p, G p ∂angularMeasure e =
      ∫⁻ φ : sphere (0 : Mom d) 1,
        ∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1, G (φ.1, normalReflection e φ.1 θ.1)
          ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
        ∂(volume : Measure (Mom d)).toSphere := by
  let K : Mom d × Mom d → ℝ≥0∞ :=
    (ball 0 1).indicator (fun p => G (pairDirections p))
  have hK : Measurable K := (hG.comp measurable_pairDirections).indicator measurableSet_ball
  have hpush : (∫⁻ p, G p ∂angularMeasure e) =
      ENNReal.ofReal (((d : ℝ) - 1) ^ 2) * ∫⁻ p, K p ∂resonantMeasure e := by
    rw [angularMeasure, lintegral_smul_measure, lintegral_map hG measurable_pairDirections,
      lintegral_indicator measurableSet_ball, smul_eq_mul]
  have hp := lintegral_resonantMeasure_polar he hd hK
  have hmass : (∫⁻ p, K p ∂resonantMeasure e) =
      (radialUnitMass (d - 2)) ^ 2 *
        ∫⁻ φ : sphere (0 : Mom d) 1,
          ∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1, G (φ.1, normalReflection e φ.1 θ.1)
            ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
          ∂(volume : Measure (Mom d)).toSphere := by
    rw [hp, ← lintegral_const_mul _ (measurable_angularIntegrand e hG).lintegral_prod_right']
    apply lintegral_congr
    intro φ
    have hφ : ‖(φ : Mom d)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using φ.2
    have hJ : Measurable (fun θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1 =>
        G (φ.1, normalReflection e φ.1 θ.1)) :=
      (measurable_angularIntegrand e hG).comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫⁻ ρ : Ioi (0 : ℝ), ∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1,
          ∫⁻ r : Ioi (0 : ℝ), (if ρ.1 < 1 ∧ r.1 < 1 then
            G (φ.1, normalReflection e φ.1 θ.1) else 0)
            ∂Measure.volumeIoiPow (d - 2)
          ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
        ∂Measure.volumeIoiPow (d - 2) := by
          apply lintegral_congr
          intro ρ
          apply lintegral_congr
          intro θ
          apply lintegral_congr
          intro r
          have hθ : ‖normalReflection e φ.1 (θ.1 : Mom d)‖ = 1 := by
            rw [LinearIsometryEquiv.norm_map]
            exact mem_sphere_zero_iff_norm.mp θ.2
          exact cutoff_pairDirections_smul hφ hθ ρ.2 r.2 G
      _ = _ := lintegral_two_radial_cutoffs _ (d - 2) hJ
  rw [hpush, hmass, ← mul_assoc, angular_radial_normalization hd, one_mul]

end WaveTurbulence.WKEL2
