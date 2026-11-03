/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.CollisionOp
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Uniform volume bounds for localized resonance kernels

Ball volumes depend only on dimension and radius. Splitting off the unit ball
about the singularity bounds the integral of `|x|⁻¹` over a ball centered
anywhere. For radii at least one the resulting bound grows at most like `R^d`.
This elementary bound suffices in DH21 Lemma 6.3.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.Resonant

/-- The dimension-dependent coefficient of Euclidean ball volume. The `toReal`
form keeps nonnegativity available without separate Gamma-function estimates. -/
@[expose] noncomputable def ballVolumeCoeff (n : ℕ) : ℝ :=
  (ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))).toReal

theorem ballVolumeCoeff_nonneg (n : ℕ) : 0 ≤ ballVolumeCoeff n := ENNReal.toReal_nonneg

/-- The volume of a ball in any nontrivial finite-dimensional real inner-product space. -/
theorem real_volume_ball_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (x : E) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.ball x R) = R ^ Module.finrank ℝ E * ballVolumeCoeff (Module.finrank ℝ E) := by
  rw [measureReal_def, InnerProductSpace.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR]
  rfl

/-- A localized `|x|⁻¹` singularity is bounded by its unit-ball integral plus volume. -/
theorem integral_ball_inv_norm_le {d : ℕ} (hd : 2 ≤ d) (a : Mom d) (R : ℝ) :
    (∫ x in Metric.ball a R, ‖x‖⁻¹) ≤
      (∫ x in Metric.ball (0 : Mom d) 1, ‖x‖⁻¹) + volume.real (Metric.ball a R) := by
  let U := Metric.ball (0 : Mom d) 1
  let S := Metric.ball a R
  have hiU := (integrableOn_ball_inv_norm hd).integrable_indicator measurableSet_ball
  have hiS : Integrable (S.indicator (fun _ : Mom d => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (s := S)
      (measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball
  have hpoint : ∀ x : Mom d,
      S.indicator (fun x => ‖x‖⁻¹) x ≤ U.indicator (fun x => ‖x‖⁻¹) x + S.indicator (fun _ => 1) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      by_cases hu : x ∈ U
      · rw [indicator_of_mem hu]
        linarith
      · rw [indicator_of_notMem hu, zero_add]
        have hnorm : 1 ≤ ‖x‖ := by
          simpa only [U, mem_ball, dist_zero_right, not_lt] using hu
        exact inv_le_one_of_one_le₀ hnorm
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
      exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hm : AEStronglyMeasurable (S.indicator (fun x : Mom d => ‖x‖⁻¹)) :=
    measurable_norm.inv.aestronglyMeasurable.indicator measurableSet_ball
  have hi := (hiU.add hiS).mono' hm (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => by positivity) _)]
    exact hpoint x)
  have h := integral_mono hi (hiU.add hiS) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hiU hiS] at h
  simpa only [U, S, integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    mul_one, measureReal_def, Measure.restrict_apply_univ] using h

/-- A constant sufficient for the localized singular radial integral. -/
@[expose] noncomputable def localizedInvNormConst (d : ℕ) : ℝ :=
  (∫ x in Metric.ball (0 : Mom d) 1, ‖x‖⁻¹) + ballVolumeCoeff d

/-- Uniformity in the ball center, with a deliberately nonsharp `R^d` growth rate. -/
theorem integral_ball_inv_norm_le_pow {d : ℕ} (hd : 2 ≤ d) (a : Mom d) {R : ℝ}
    (hR : 1 ≤ R) :
    (∫ x in Metric.ball a R, ‖x‖⁻¹) ≤ localizedInvNormConst d * R ^ d := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (show 0 < d by omega))
  have hvol := real_volume_ball_eq a (le_trans (by norm_num) hR)
  rw [finrank_euclideanSpace_fin] at hvol
  refine (integral_ball_inv_norm_le hd a R).trans ?_
  rw [hvol, localizedInvNormConst, add_mul]
  have hp : 1 ≤ R ^ d := one_le_pow₀ hR
  have hn : 0 ≤ ∫ x in Metric.ball (0 : Mom d) 1, ‖x‖⁻¹ :=
    integral_nonneg fun _ => inv_nonneg.mpr (norm_nonneg _)
  exact add_le_add (le_mul_of_one_le_right hn hp) (le_of_eq (mul_comm _ _))

/-- Local integrability at the origin also gives integrability on a ball with any center. -/
theorem integrableOn_ball_inv_norm_center {d : ℕ} (hd : 2 ≤ d) (a : Mom d) (R : ℝ) :
    IntegrableOn (fun x : Mom d => ‖x‖⁻¹) (Metric.ball a R) := by
  have h0 : IntegrableOn (fun x : Mom d => ‖x‖⁻¹) (Metric.ball 0 (|R| + ‖a‖ + 1)) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)
      (by rw [finrank_euclideanSpace_fin]; omega) ?_ ?_ ?_
    · rw [finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < d)
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]
    · exact measurable_norm.inv.aestronglyMeasurable
  apply h0.mono_set
  intro x hx
  change dist x a < R at hx
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖x‖ ≤ dist x a + ‖a‖ := by
      simpa only [dist_zero_right] using dist_triangle x a (0 : Mom d)
    _ < R + ‖a‖ := by linarith only [hx]
    _ ≤ |R| + ‖a‖ + 1 := by linarith [le_abs_self R]

/-- Ball volume in momentum space. -/
theorem real_volume_mom_ball_eq {d : ℕ} (hd : 0 < d) (a : Mom d) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.ball a R) = R ^ d * ballVolumeCoeff d := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  simpa only [finrank_euclideanSpace_fin] using real_volume_ball_eq a hR

/-- Hyperplane ball volume is independent of the hyperplane's orientation. -/
theorem real_volume_perp_ball_eq {d : ℕ} (hd : 2 ≤ d) {ℓ : Mom d} (hℓ : ℓ ≠ 0)
    (c : ↥(ℝ ∙ ℓ)ᗮ) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.ball c R) = R ^ (d - 1) * ballVolumeCoeff (d - 1) := by
  have : Nontrivial ↥(ℝ ∙ ℓ)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_perp hℓ]; omega)
  simpa only [finrank_perp hℓ] using real_volume_ball_eq c hR

/-- A convenient common `R^d` upper bound for a hyperplane support ball. -/
theorem real_volume_perp_ball_two_mul_le {d : ℕ} (hd : 2 ≤ d) {ℓ : Mom d}
    (hℓ : ℓ ≠ 0) (c : ↥(ℝ ∙ ℓ)ᗮ) {R : ℝ} (hR : 1 ≤ R) :
    volume.real (Metric.ball c (2 * R)) ≤
      (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) * R ^ d := by
  have hp := ballVolumeCoeff_nonneg (d - 1)
  have hpow : R ^ (d - 1) ≤ R ^ d := pow_le_pow_right₀ hR (Nat.sub_le d 1)
  rw [real_volume_perp_ball_eq hd hℓ c (by linarith), mul_pow]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) hp).trans_eq (by ring)

end WaveTurbulence.Resonant
