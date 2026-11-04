/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AngularSlice
public import WaveTurbulence.Foundations.WKEL2.ResonantPolar
public import WaveTurbulence.Foundations.WKEL2.ResonantSymmetry

/-!
# Spherical-average representation of the first loss kernel

Research-note Proposition 6, before the weighted Cauchy–Schwarz estimate.
The normalization here omits the delta factor one half.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The absolute spherical average, with the factor one half kept outside. -/
@[expose] def sphericalLossAverage (h : Mom d → ℝ) (k w : Mom d) : ℝ≥0∞ :=
  ∫⁻ θ : sphere (0 : Mom d) 1,
    ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • (θ : Mom d))| *
      positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ
        ∂(volume : Measure (Mom d)).toSphere

/-- Jointly measurable integrand of the spherical average. -/
theorem measurable_sphericalLossIntegrand {h : Mom d → ℝ} (hh : Measurable h) (k : Mom d) :
    Measurable (fun p : Mom d × sphere (0 : Mom d) 1 =>
      ENNReal.ofReal |h (k + ⟪(p.2.1 : Mom d), p.1⟫_ℝ • (p.2.1 : Mom d))| *
        positiveRayDensity (d - 2) ⟪(p.2.1 : Mom d), p.1⟫_ℝ) :=
  (hh.abs.ennreal_ofReal.comp (by fun_prop)).mul
    ((measurable_positiveRayDensity _).comp (by fun_prop))

theorem measurable_sphericalLossAverage {h : Mom d → ℝ} (hh : Measurable h) (k : Mom d) :
    Measurable (sphericalLossAverage h k) :=
  (measurable_sphericalLossIntegrand hh k).lintegral_prod_right'

/-- Tonelli and a positive half-space slice give the spherical-average formula. -/
theorem lintegral_lossOne_spherical {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {g h : Mom d → ℝ} (hg : Measurable g) (hh : Measurable h) (k : Mom d) :
    (∫⁻ p, ENNReal.ofReal |g (k + p.1 + p.2)| * ENNReal.ofReal |h (k + p.2)|
      ∂resonantMeasure e) =
      ∫⁻ w : Mom d, ENNReal.ofReal |g (k + w)| * sphericalLossAverage h k w := by
  let F : Mom d × Mom d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |g (k + p.1 + p.2)| * ENNReal.ofReal |h (k + p.2)|
  have hF : Measurable F :=
    (hg.abs.ennreal_ofReal.comp (by fun_prop)).mul (hh.abs.ennreal_ofReal.comp (by fun_prop))
  have hswap : (∫⁻ p, F p ∂resonantMeasure e) =
      ∫⁻ p, F (p.2, p.1) ∂resonantMeasure e := by
    have ht := lintegral_map (μ := resonantMeasure e) hF (measurable_swap (α := Mom d) (β := Mom d))
    rw [map_swap_resonantMeasure he hd] at ht
    simpa only [Prod.swap] using ht
  have hpolar : (∫⁻ p : Mom d × Mom d, F (p.2, p.1) ∂resonantMeasure e) =
      ∫⁻ θ : sphere (0 : Mom d) 1, ∫⁻ r : Ioi (0 : ℝ),
        ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (normalReflection e θ.1 w, r.1 • θ.1)
          ∂volume ∂Measure.volumeIoiPow (d - 2) ∂(volume : Measure (Mom d)).toSphere := by
    simpa only [Function.comp_def, Prod.swap] using
      lintegral_resonantMeasure_polar_left e hd (hF.comp measurable_swap)
  have hslice (θ : sphere (0 : Mom d) 1) :
      (∫⁻ r : Ioi (0 : ℝ), ∫⁻ w : ↥(ℝ ∙ e)ᗮ,
        F (normalReflection e θ.1 w, r.1 • θ.1) ∂volume ∂Measure.volumeIoiPow (d - 2)) =
      ∫⁻ w : Mom d, positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ *
        (ENNReal.ofReal |g (k + w)| * ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • θ.1)|) := by
    have hθ : ‖(θ : Mom d)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
    have hθ0 : (θ : Mom d) ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hθ
    have hK : Measurable (fun q : ℝ × Mom d =>
        ENNReal.ofReal |g (k + q.2)| * ENNReal.ofReal |h (k + q.1 • θ.1)|) :=
      (hg.abs.ennreal_ofReal.comp (by fun_prop)).mul (hh.abs.ennreal_ofReal.comp (by fun_prop))
    have hs := lintegral_angularSlice he hθ0 (d - 2) hK
    simp only [unitVec_of_norm_one hθ] at hs
    convert hs using 1
    apply lintegral_congr
    intro r
    apply lintegral_congr
    intro w
    dsimp only [F]
    rw [show k + normalReflection e θ.1 w + r.1 • θ.1 =
      k + (r.1 • θ.1 + normalReflection e θ.1 w) by abel]
  have hJoint : Measurable (fun p : sphere (0 : Mom d) 1 × Mom d =>
      positiveRayDensity (d - 2) ⟪(p.1.1 : Mom d), p.2⟫_ℝ *
        (ENNReal.ofReal |g (k + p.2)| *
          ENNReal.ofReal |h (k + ⟪(p.1.1 : Mom d), p.2⟫_ℝ • p.1.1)|)) :=
    ((measurable_positiveRayDensity _).comp (by fun_prop)).mul
      ((hg.abs.ennreal_ofReal.comp (by fun_prop)).mul (hh.abs.ennreal_ofReal.comp (by fun_prop)))
  change (∫⁻ p, F p ∂resonantMeasure e) = _
  rw [hswap, hpolar]
  calc
    _ = ∫⁻ θ : sphere (0 : Mom d) 1, ∫⁻ w : Mom d,
        positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ *
          (ENNReal.ofReal |g (k + w)| * ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • θ.1)|)
          ∂volume ∂(volume : Measure (Mom d)).toSphere := by
      exact lintegral_congr hslice
    _ = ∫⁻ w : Mom d, ∫⁻ θ : sphere (0 : Mom d) 1,
        positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ *
          (ENNReal.ofReal |g (k + w)| * ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • θ.1)|)
          ∂(volume : Measure (Mom d)).toSphere ∂volume :=
      by
        exact lintegral_lintegral_swap (μ := (volume : Measure (Mom d)).toSphere)
          (ν := (volume : Measure (Mom d))) hJoint.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      dsimp only [sphericalLossAverage]
      have hRay : Continuous (fun θ : sphere (0 : Mom d) 1 =>
          k + ⟪(θ : Mom d), w⟫_ℝ • θ.1) := by fun_prop
      have hAxial : Continuous (fun θ : sphere (0 : Mom d) 1 => ⟪(θ : Mom d), w⟫_ℝ) := by fun_prop
      have hm : Measurable (fun θ : sphere (0 : Mom d) 1 =>
          ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • θ.1)| *
            positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ) :=
        (hh.abs.ennreal_ofReal.comp hRay.measurable).mul
          ((measurable_positiveRayDensity _).comp hAxial.measurable)
      calc
        _ = ∫⁻ θ : sphere (0 : Mom d) 1, ENNReal.ofReal |g (k + w)| *
            (ENNReal.ofReal |h (k + ⟪(θ : Mom d), w⟫_ℝ • θ.1)| *
              positiveRayDensity (d - 2) ⟪(θ : Mom d), w⟫_ℝ)
              ∂(volume : Measure (Mom d)).toSphere := by
          apply lintegral_congr
          intro θ
          ac_rfl
        _ = _ := lintegral_const_mul (ENNReal.ofReal |g (k + w)|) hm

end WaveTurbulence.WKEL2
