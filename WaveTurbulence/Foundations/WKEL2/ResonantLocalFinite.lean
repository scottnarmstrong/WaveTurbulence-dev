/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure

/-!
# Local finiteness of resonant measure

Compact sets of resonant pairs are contained in products of bounded balls.
The inverse norm is locally integrable in dimension at least two.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The singular density of resonant measure is locally integrable for `d ≥ 2`. -/
theorem locallyIntegrable_inv_norm (hd : 2 ≤ d) :
    LocallyIntegrable (fun a : Mom d => ‖a‖⁻¹) := by
  have hfin : Module.finrank ℝ (Mom d) = d := finrank_euclideanSpace_fin
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by omega) ?_ ?_ ?_
  · rw [hfin]
    exact_mod_cast (by omega : 1 < d)
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]
  · exact measurable_norm.inv.aestronglyMeasurable

/-- The fixed-coordinate chart preserves the radial product norm. -/
theorem resonantChart_preimage_ball (e : Mom d) (R : ℝ) :
    resonantChart e ⁻¹' ball 0 R =
      (ball 0 R : Set (Mom d)) ×ˢ (ball 0 R : Set ↥(ℝ ∙ e)ᗮ) := by
  ext p
  simp only [mem_preimage, mem_ball_zero_iff, mem_prod, resonantChart,
    Prod.norm_def, LinearIsometryEquiv.norm_map, Submodule.norm_coe, max_lt_iff]

/-- Exact mass of a centered ball, computed in fixed hyperplane coordinates. -/
theorem resonantMeasure_ball (e : Mom d) (R : ℝ) :
    resonantMeasure e (ball 0 R) =
      (∫⁻ a in ball (0 : Mom d) R, ENNReal.ofReal (‖a‖⁻¹)) *
        volume (ball (0 : ↥(ℝ ∙ e)ᗮ) R) := by
  rw [resonantMeasure, Measure.map_apply (measurable_resonantChart e) measurableSet_ball,
    resonantChart_preimage_ball, withDensity_apply _
      (measurableSet_ball.prod measurableSet_ball), ← Measure.prod_restrict]
  have hdens : Measurable (fun p : Mom d × ↥(ℝ ∙ e)ᗮ => ENNReal.ofReal (‖p.1‖⁻¹)) :=
    (measurable_norm.comp measurable_fst).inv.ennreal_ofReal
  rw [lintegral_prod (fun p : Mom d × ↥(ℝ ∙ e)ᗮ => ENNReal.ofReal (‖p.1‖⁻¹))
    (μ := volume.restrict (ball 0 R)) (ν := volume.restrict (ball 0 R)) hdens.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  exact lintegral_mul_const _ measurable_norm.inv.ennreal_ofReal

/-- Every centered ball has finite resonant mass in dimension at least two. -/
theorem resonantMeasure_ball_lt_top (e : Mom d) (hd : 2 ≤ d) (R : ℝ) :
    resonantMeasure e (ball 0 R) < ⊤ := by
  rw [resonantMeasure_ball]
  have hi := ((locallyIntegrable_inv_norm hd).integrableOn_isCompact
    (isCompact_closedBall (0 : Mom d) R)).mono_set ball_subset_closedBall
  have hf : (∫⁻ a in ball (0 : Mom d) R, ENNReal.ofReal (‖a‖⁻¹)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)).mp
      hi.hasFiniteIntegral
  exact ENNReal.mul_lt_top hf measure_ball_lt_top

/-- The resonant measure is finite on compact sets, hence locally finite. -/
theorem resonantMeasure_finiteOnCompacts (e : Mom d) (hd : 2 ≤ d) :
    IsFiniteMeasureOnCompacts (resonantMeasure e) where
  lt_top_of_isCompact := by
    intro K hK
    obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_lt
    exact (measure_mono (fun x hx => mem_ball_zero_iff.mpr (hR x hx))).trans_lt
      (resonantMeasure_ball_lt_top e hd R)

end WaveTurbulence.WKEL2
