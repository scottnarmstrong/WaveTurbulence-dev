/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VdCB.CircleLocalization
public import WaveTurbulence.Foundations.VdCB.CircleSourceBounds
public import WaveTurbulence.Foundations.NumberTheory.ReflectedNegativePhase
public import WaveTurbulence.Foundations.NumberTheory.CircleSourceScale
import Mathlib.Tactic

/-!
# Actual reflected circle source derivative bounds, using the shared smooth localization.
-/

public section

open Set
open scoped ContDiff
namespace WaveTurbulence.NumberTheory

theorem reflected_source_curvature_bounds {R h U D x : ℝ} (hU : 0 < U) (hUR : 3*U ≤ R) (hh : 0 < h)
    (hx : D-x ∈ Icc U (2*U)) :
    (h*Real.sqrt R)*U^(-((3:ℝ)/2))/8 ≤
      deriv (deriv (fun t => -VdCB.circleSourceExtension R h U hU (D-t))) x ∧
    deriv (deriv (fun t => -VdCB.circleSourceExtension R h U hU (D-t))) x ≤
      (h*Real.sqrt R)*U^(-((3:ℝ)/2)) := by
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  have hs := VdCB.contDiff_circleSourceExtension hU hUR h
  have hs2 : ContDiff ℝ 2 (VdCB.circleSourceExtension R h U hU) := hs.of_le (by simp)
  rw [deriv_deriv_neg_comp_sub_const hs2]
  have he := VdCB.iteratedDeriv_circleSourceExtension (R := R) (h := h) hU hx 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
  rw [he]
  have hb := VdCB.neg_deriv_deriv_circlePhase_bounds hU hUR hh hx
  rw [circle_source_lower_curvature_scale hR hU,circle_source_upper_curvature_scale hR hU] at hb
  exact hb

theorem reflected_source_third_bound {R h U D x : ℝ} (hU : 0 < U) (hUR : 3*U ≤ R) (hh : 0 < h)
    (hx : D-x ∈ Icc U (2*U)) :
    |iteratedDeriv 3 (fun t => -VdCB.circleSourceExtension R h U hU (D-t)) x| ≤
      3*(h*Real.sqrt R)*U^(-((5:ℝ)/2)) := by
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  have hs := VdCB.contDiff_circleSourceExtension hU hUR h
  have hs3 : ContDiff ℝ 3 (VdCB.circleSourceExtension R h U hU) := hs.of_le (by simp)
  rw [iteratedDeriv_three_neg_comp_sub_const hs3]
  rw [VdCB.iteratedDeriv_circleSourceExtension (R := R) (h := h) hU hx]
  have hb := VdCB.abs_iteratedDeriv_three_circlePhase_le hU hUR hh hx
  rw [circle_source_third_derivative_scale hR hU] at hb
  exact hb

theorem reflected_source_first_bounds {R h U D x : ℝ} (hU : 0 < U) (hUR : 3*U ≤ R) (hh : 0 < h)
    (hx : D-x ∈ Icc U (2*U)) :
    0 ≤ deriv (fun t => -VdCB.circleSourceExtension R h U hU (D-t)) x ∧
      deriv (fun t => -VdCB.circleSourceExtension R h U hU (D-t)) x ≤
        (h*Real.sqrt R)*U^(-((1:ℝ)/2)) := by
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  have hu : D-x ∈ Ioo 0 R := ⟨hU.trans_le hx.1,by linarith only [hx.2,hUR,hU]⟩
  have hs := VdCB.contDiff_circleSourceExtension hU hUR h
  rw [deriv_neg_comp_sub_const (hs.differentiable (by simp))]
  have he := VdCB.iteratedDeriv_circleSourceExtension (R := R) (h := h) hU hx 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
  rw [he,(VdCB.hasDerivAt_circlePhase_rpow hR hu).deriv]
  unfold VdCB.circleSourceFirst
  have hDlo : R*U ≤ 2*R*(D-x)-(D-x)^2 := by
    have h1 := mul_le_mul_of_nonneg_right (show R ≤ 2*R-(D-x) by linarith only [hu.2]) hu.1.le
    have h2 := mul_le_mul_of_nonneg_left hx.1 hR.le
    nlinarith only [h1,h2]
  have hheight : 0 < 2*R*(D-x)-(D-x)^2 := (mul_pos hR hU).trans_le hDlo
  have hRu : 0 ≤ R-(D-x) := sub_nonneg.mpr hu.2.le
  constructor
  · positivity
  · calc
      _ ≤ h*R*(2*R*(D-x)-(D-x)^2)^(-((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (show R-(D-x) ≤ R by linarith only [hu.1]) hh.le) (by positivity)
      _ ≤ h*R*(R*U)^(-((1:ℝ)/2)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (mul_pos hR hU) hDlo (by norm_num)) (by positivity)
      _ = _ := circle_source_first_derivative_scale hR hU h

end WaveTurbulence.NumberTheory
