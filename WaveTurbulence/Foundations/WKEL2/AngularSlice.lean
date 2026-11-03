/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PositiveRayDensity
public import WaveTurbulence.Foundations.WKEL2.AngularProduct

/-!
# Slicing in the measurable fixed-hyperplane angular chart
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Volume coordinates obtained by rotating the fixed transverse hyperplane. -/
@[expose] def angularSliceEquiv {e θ : Mom d} (he : ‖e‖ = 1) (hθ : θ ≠ 0) :
    ℝ × ↥(ℝ ∙ e)ᗮ ≃ᵐ Mom d :=
  ((MeasurableEquiv.refl ℝ).prodCongr (hyperplaneChart he hθ).toMeasurableEquiv).trans
    (sliceEquiv hθ)

theorem angularSliceEquiv_apply {e θ : Mom d} (he : ‖e‖ = 1) (hθ : θ ≠ 0)
    (t : ℝ) (w : ↥(ℝ ∙ e)ᗮ) :
    angularSliceEquiv he hθ (t, w) = t • unitVec θ + normalReflection e θ w := by
  rw [angularSliceEquiv, MeasurableEquiv.trans_apply, sliceEquiv_apply]
  rfl

theorem measurePreserving_angularSliceEquiv {e θ : Mom d} (he : ‖e‖ = 1) (hθ : θ ≠ 0) :
    MeasurePreserving (angularSliceEquiv he hθ) (volume.prod volume) volume :=
  (measurePreserving_sliceEquiv hθ).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_hyperplaneChart he hθ))

/-- The axial scalar is recovered by taking an inner product. -/
theorem inner_angularSliceEquiv {e θ : Mom d} (he : ‖e‖ = 1) (hθ : θ ≠ 0)
    (t : ℝ) (w : ↥(ℝ ∙ e)ᗮ) :
    ⟪unitVec θ, angularSliceEquiv he hθ (t, w)⟫_ℝ = t := by
  have hz : ⟪unitVec θ, normalReflection e θ w⟫_ℝ = 0 := by
    rw [← coe_hyperplaneChart he hθ w]
    exact inner_unitVec_eq_zero_of_mem_perp _
  rw [angularSliceEquiv_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_unitVec hθ, one_pow, mul_one, hz, add_zero]

/-- Converting a positive radial integral and transverse integral into volume. -/
theorem lintegral_angularSlice {e θ : Mom d} (he : ‖e‖ = 1) (hθ : θ ≠ 0)
    (n : ℕ) {F : ℝ × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ r : Ioi (0 : ℝ), ∫⁻ w : ↥(ℝ ∙ e)ᗮ,
      F (r.1, r.1 • unitVec θ + normalReflection e θ w) ∂volume
        ∂Measure.volumeIoiPow n) =
      ∫⁻ x : Mom d, positiveRayDensity n ⟪unitVec θ, x⟫_ℝ *
        F (⟪unitVec θ, x⟫_ℝ, x) := by
  let T := angularSliceEquiv he hθ
  let G : Mom d → ℝ≥0∞ := fun x => positiveRayDensity n ⟪unitVec θ, x⟫_ℝ *
    F (⟪unitVec θ, x⟫_ℝ, x)
  have hInner : Measurable (fun x : Mom d => ⟪unitVec θ, x⟫_ℝ) := by fun_prop
  have hG : Measurable G :=
    ((measurable_positiveRayDensity n).comp hInner).mul (hF.comp (hInner.prodMk measurable_id))
  have hcomp : Measurable (fun p : ℝ × ↥(ℝ ∙ e)ᗮ => F (p.1, T p)) :=
    hF.comp (measurable_fst.prodMk T.measurable)
  have hm : Measurable (fun t : ℝ => ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (t, T (t, w))) :=
    hcomp.lintegral_prod_right'
  have hchange := (measurePreserving_angularSliceEquiv he hθ).lintegral_comp_emb
    T.measurableEmbedding G
  calc
    _ = ∫⁻ r : Ioi (0 : ℝ), (∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (r.1, T (r.1, w)))
        ∂Measure.volumeIoiPow n := by simp only [T, angularSliceEquiv_apply]
    _ = ∫⁻ t : ℝ, positiveRayDensity n t * ∫⁻ w : ↥(ℝ ∙ e)ᗮ, F (t, T (t, w)) :=
      (lintegral_positiveRayDensity n hm).symm
    _ = ∫⁻ p : ℝ × ↥(ℝ ∙ e)ᗮ, G (T p) ∂volume.prod volume := by
      have hGT : Measurable (fun p : ℝ × ↥(ℝ ∙ e)ᗮ => G (T p)) := hG.comp T.measurable
      rw [lintegral_prod _ hGT.aemeasurable]
      apply lintegral_congr
      intro t
      have hmt : Measurable (fun w : ↥(ℝ ∙ e)ᗮ => F (t, T (t, w))) :=
        hcomp.comp (measurable_const.prodMk measurable_id)
      simp only [G, T, inner_angularSliceEquiv]
      exact (lintegral_const_mul _ hmt).symm
    _ = _ := hchange

end WaveTurbulence.WKEL2
