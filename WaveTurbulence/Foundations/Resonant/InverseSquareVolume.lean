/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalizedVolume

/-!
# The inverse-square singularity in dimension at least three

The small-energy error in DH21 Lemma 6.3(2) introduces `|x|⁻²`.
Its integral over a localized ball has a bound uniform in the center.
-/

public section

open MeasureTheory Filter Topology Set Metric

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Local integrability of the inverse-square norm in `d≥3`. -/
theorem integrableOn_ball_inv_norm_sq (hd : 3 ≤ d) (R : ℝ) :
    IntegrableOn (fun x : Mom d => (‖x‖⁻¹) ^ 2) (Metric.ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
    (by rw [finrank_euclideanSpace_fin]; omega) ?_ ?_ ?_
  · rw [finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 < d)
  · refine Eventually.of_forall fun x => ?_
    simp only [Real.rpow_neg (norm_nonneg x), Real.rpow_two, inv_pow, norm_inv, norm_pow, norm_norm, one_mul]
    exact le_rfl
  · exact (measurable_norm.inv.pow_const 2).aestronglyMeasurable

/-- Integrability on a ball with any center. -/
theorem integrableOn_ball_inv_norm_sq_center (hd : 3 ≤ d) (a : Mom d) (R : ℝ) :
    IntegrableOn (fun x : Mom d => (‖x‖⁻¹) ^ 2) (Metric.ball a R) := by
  apply (integrableOn_ball_inv_norm_sq hd (|R| + ‖a‖ + 1)).mono_set
  intro x hx
  change dist x a < R at hx
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖x‖ ≤ dist x a + ‖a‖ := by
      simpa only [dist_zero_right] using dist_triangle x a (0 : Mom d)
    _ < R + ‖a‖ := by linarith only [hx]
    _ ≤ |R| + ‖a‖ + 1 := by linarith [le_abs_self R]

/-- Elementary localized inverse-square bound. -/
theorem integral_ball_inv_norm_sq_le (hd : 3 ≤ d) (a : Mom d) (R : ℝ) :
    (∫ x in Metric.ball a R, (‖x‖⁻¹) ^ 2) ≤
      (∫ x in Metric.ball (0 : Mom d) 1, (‖x‖⁻¹) ^ 2) + volume.real (Metric.ball a R) := by
  let U := Metric.ball (0 : Mom d) 1
  let S := Metric.ball a R
  have hiU := (integrableOn_ball_inv_norm_sq hd 1).integrable_indicator measurableSet_ball
  have hiS : Integrable (S.indicator (fun _ : Mom d => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (s := S) measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  have hi := (integrableOn_ball_inv_norm_sq_center hd a R).integrable_indicator measurableSet_ball
  have hp : ∀ x : Mom d,
      S.indicator (fun x => (‖x‖⁻¹) ^ 2) x ≤
        U.indicator (fun x => (‖x‖⁻¹) ^ 2) x + S.indicator (fun _ => 1) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      by_cases hu : x ∈ U
      · rw [indicator_of_mem hu]
        linarith
      · rw [indicator_of_notMem hu, zero_add]
        have hn : 1 ≤ ‖x‖ := by simpa only [U, mem_ball, dist_zero_right, not_lt] using hu
        exact pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_le_one_of_one_le₀ hn)
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
      exact indicator_nonneg (fun _ _ => sq_nonneg _) _
  have h := integral_mono hi (hiU.add hiS) hp
  simp only [Pi.add_apply] at h
  rw [integral_add hiU hiS] at h
  simpa only [U, S, integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    mul_one, measureReal_def, Measure.restrict_apply_univ] using h

/-- A dimension-dependent coefficient for localized inverse-square integration. -/
@[expose] noncomputable def localizedInvNormSqConst (d : ℕ) : ℝ :=
  (∫ x in Metric.ball (0 : Mom d) 1, (‖x‖⁻¹) ^ 2) + ballVolumeCoeff d

/-- Uniform bound at radii at least one. -/
theorem integral_ball_inv_norm_sq_le_pow (hd : 3 ≤ d) (a : Mom d) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in Metric.ball a R, (‖x‖⁻¹) ^ 2) ≤ localizedInvNormSqConst d * R ^ d := by
  refine (integral_ball_inv_norm_sq_le hd a R).trans ?_
  rw [real_volume_mom_ball_eq (by omega) a (le_trans (by norm_num) hR), localizedInvNormSqConst, add_mul]
  have hp : 1 ≤ R ^ d := one_le_pow₀ hR
  have hn : 0 ≤ ∫ x in Metric.ball (0 : Mom d) 1, (‖x‖⁻¹) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact add_le_add (le_mul_of_one_le_right hn hp) (le_of_eq (mul_comm _ _))

end WaveTurbulence.Resonant
