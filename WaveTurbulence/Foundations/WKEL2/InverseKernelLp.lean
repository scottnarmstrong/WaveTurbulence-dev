/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialWeight
public import WaveTurbulence.Foundations.WKE.CollisionOp

/-!
# Near and far parts of the inverse-norm kernel

The singular kernel in Lemma 4(a) is integrable near zero in dimension at
least two and belongs to Lᵖ away from zero when `p` exceeds the dimension.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The inverse-norm kernel restricted to the unit ball. -/
@[expose] def inverseNear (x : Mom d) : ℝ :=
  (ball 0 1).indicator (fun x => ‖x‖⁻¹) x

/-- The inverse-norm kernel outside the open unit ball. -/
@[expose] def inverseFar (x : Mom d) : ℝ :=
  (ball 0 1)ᶜ.indicator (fun x => ‖x‖⁻¹) x

theorem inverseNear_nonneg (x : Mom d) : 0 ≤ inverseNear x :=
  indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _

theorem inverseFar_nonneg (x : Mom d) : 0 ≤ inverseFar x :=
  indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _

/-- Exact decomposition, including zero and the unit sphere. -/
theorem inverseNear_add_inverseFar (x : Mom d) : inverseNear x + inverseFar x = ‖x‖⁻¹ := by
  exact congrFun (indicator_self_add_compl (ball 0 1) (fun x : Mom d => ‖x‖⁻¹)) x

/-- Local integrability of the singular near part. -/
theorem integrable_inverseNear (hd : 2 ≤ d) : Integrable (inverseNear : Mom d → ℝ) :=
  (integrableOn_ball_inv_norm hd).integrable_indicator measurableSet_ball

/-- Measurability of the far part. -/
theorem measurable_inverseFar : Measurable (inverseFar : Mom d → ℝ) :=
  measurable_norm.inv.indicator measurableSet_ball.compl

/-- The far part is in Lᵖ for every exponent greater than the dimension. -/
theorem memLp_inverseFar (p : ℝ) (hp : (d : ℝ) < p) :
    MemLp (inverseFar : Mom d → ℝ) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := (Nat.cast_nonneg d).trans_lt hp
  apply (integrable_norm_rpow_iff measurable_inverseFar.aestronglyMeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).mp
  have hi := (integrable_one_add_norm (μ := (volume : Measure (Mom d)))
    (by simpa only [finrank_euclideanSpace_fin] using hp)).const_mul ((2 : ℝ) ^ p)
  have hm : AEStronglyMeasurable (fun x : Mom d => ‖inverseFar x‖ ^ p) :=
    (measurable_inverseFar.norm.pow_const p).aestronglyMeasurable
  have hpow : Integrable (fun x : Mom d => ‖inverseFar x‖ ^ p) := by
    refine hi.mono' hm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hx : x ∈ ball (0 : Mom d) 1
    · simp only [inverseFar, indicator_of_notMem (show x ∉ (ball (0 : Mom d) 1)ᶜ from fun h => h hx), norm_zero,
        Real.zero_rpow hp0.ne']
      positivity
    · have hx1 : 1 ≤ ‖x‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hx)
      have hx0 : 0 < ‖x‖ := zero_lt_one.trans_le hx1
      rw [inverseFar, indicator_of_mem hx, Real.norm_of_nonneg (inv_nonneg.mpr hx0.le),
        Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
      exact rpow_neg_le_of_le_mul (by positivity) hx0 (by norm_num) hp0.le
        (by linarith only [hx1])
  simpa only [ENNReal.toReal_ofReal hp0.le] using hpow

end WaveTurbulence.WKEL2
