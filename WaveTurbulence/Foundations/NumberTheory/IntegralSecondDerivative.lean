/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.IntegralSecondDerivativeSide
import WaveTurbulence.Foundations.VdCB.FrequencyIntegration
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Uniform second-derivative oscillatory integral test

An actual positive or negative curvature lower bound gives `4/sqrt(mu)`
on every closed interval. The result covers critical points at or near an
endpoint and has no derivative-separation hypothesis.
-/

public section

namespace WaveTurbulence.NumberTheory

open MeasureTheory Set

/-- The integral form of the second-derivative test for positive curvature,
uniformly including all endpoint positions of the critical point. -/
theorem norm_integral_expPhase_le_of_second_deriv_pos {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hcurv : ∀ x ∈ Icc a b, mu ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 4/Real.sqrt mu := by
  let r : ℝ := 1/Real.sqrt mu
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpi : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have htail : 1/(Real.pi*Real.sqrt mu) ≤ r := by
    have hd : Real.sqrt mu ≤ Real.pi*Real.sqrt mu := by
      nlinarith only [mul_le_mul_of_nonneg_right hpi hs.le]
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hs hd
  rw [show 4/Real.sqrt mu = 4*r by dsimp only [r]; ring]
  by_cases ha : 0 ≤ deriv f a
  · have hh := norm_integral_expPhase_le_of_second_pos_left hf hab hmu ha hcurv
    linarith only [hh,htail,hr]
  by_cases hb : deriv f b ≤ 0
  · have hh := norm_integral_expPhase_le_of_second_pos_right hf hab hmu hb hcurv
    linarith only [hh,htail,hr]
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨c,hc,hzero⟩ := (intermediate_value_Icc hab hf1.continuous.continuousOn)
    (show (0:ℝ) ∈ Icc (deriv f a) (deriv f b) from
      ⟨(lt_of_not_ge ha).le,(lt_of_not_ge hb).le⟩)
  have hleft := norm_integral_expPhase_le_of_second_pos_right hf hc.1 hmu hzero.le
    (fun x hx => hcurv x ⟨hx.1,hx.2.trans hc.2⟩)
  have hright := norm_integral_expPhase_le_of_second_pos_left hf hc.2 hmu hzero.ge
    (fun x hx => hcurv x ⟨hc.1.trans hx.1,hx.2⟩)
  have hcf : Continuous (fun x => expPhase (f x)) := (VdCB.contDiff_expPhase 0).continuous.comp hf.continuous
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcf.intervalIntegrable a c) (hcf.intervalIntegrable c b)
  rw [← he]
  apply ((norm_add_le _ _).trans (add_le_add hleft hright)).trans
  linarith only [htail]

/-- Exact conjugation invariance of the normalized oscillatory integral. -/
theorem norm_integral_expPhase_neg (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ x in a..b, expPhase (-f x)‖ = ‖∫ x in a..b, expPhase (f x)‖ := by
  simp_rw [← conj_expPhase]
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab,
    integral_conj,RCLike.norm_conj]

/-- The negative-curvature integral test, by exact phase conjugation. -/
theorem norm_integral_expPhase_le_of_second_deriv_neg {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv f) x ≤ -mu) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 4/Real.sqrt mu := by
  have hfirst : deriv (fun x => -f x) = fun x => -deriv f x := by
    funext x
    exact deriv.fun_neg
  have he := norm_integral_expPhase_le_of_second_deriv_pos hf.neg hab hmu (fun x hx => by
    rw [hfirst,deriv.fun_neg]
    have hh := hcurv x hx
    linarith only [hh])
  rw [norm_integral_expPhase_neg f hab] at he
  exact he

/-- Positive-curvature bound uniform in every real Poisson frequency,
including frequencies equal to an endpoint derivative. -/
theorem norm_integral_expPhase_sub_frequency_le_of_second_pos {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hcurv : ∀ x ∈ Icc a b, mu ≤ deriv (deriv f) x) (nu : ℝ) :
    ‖∫ x in a..b, expPhase (f x-nu*x)‖ ≤ 4/Real.sqrt mu := by
  apply norm_integral_expPhase_le_of_second_deriv_pos
    (hf.sub (contDiff_const.mul contDiff_id)) hab hmu
  intro x hx
  simp only [id_eq]
  rw [VdCB.deriv_deriv_sub_frequency hf]
  exact hcurv x hx

/-- Negative-curvature bound uniform in every real Poisson frequency. -/
theorem norm_integral_expPhase_sub_frequency_le_of_second_neg {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    (hcurv : ∀ x ∈ Icc a b, deriv (deriv f) x ≤ -mu) (nu : ℝ) :
    ‖∫ x in a..b, expPhase (f x-nu*x)‖ ≤ 4/Real.sqrt mu := by
  apply norm_integral_expPhase_le_of_second_deriv_neg
    (hf.sub (contDiff_const.mul contDiff_id)) hab hmu
  intro x hx
  simp only [id_eq]
  rw [VdCB.deriv_deriv_sub_frequency hf]
  exact hcurv x hx

end WaveTurbulence.NumberTheory
