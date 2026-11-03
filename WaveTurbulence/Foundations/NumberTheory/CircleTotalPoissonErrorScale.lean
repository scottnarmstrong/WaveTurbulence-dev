/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CirclePoissonErrorScale
public import WaveTurbulence.Foundations.NumberTheory.CircleSummedStationaryScale
public import WaveTurbulence.Foundations.NumberTheory.CircleGuardErrorScale
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Total explicit B-process error at the balanced circle scales

This scalar bound combines the actual sharp Poisson error, guard cost,
separated-frequency cost and stationary remainder, before any use of a
circle exponential-sum conclusion.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- All explicit quantitative B errors fit the improved local powers. -/
theorem circle_scale_total_poisson_error_le {w U : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U)
    (hUw : U ≤ w^2) (hwU : w ≤ U^2) (N : ℕ)
    (hN : (N:ℝ)+1 ≤ 3*(w*U^(-((1:ℝ)/2)))) :
    let r := stationaryBalancingRadius w U
    let mu := w*U^(-((3:ℝ)/2))/8
    let Lam := w*U^(-((3:ℝ)/2))
    ((2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1)+
      (4*Lam*r+2)*(4/Real.sqrt mu)+((N:ℝ)+1)/(Real.pi*(Lam*r))+
      ((N:ℝ)+1)*(2*Real.pi/3*(3*w*U^(-((5:ℝ)/2)))*r^4+4/(Real.pi*(mu*r))) ≤
      2320*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  let r := stationaryBalancingRadius w U
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  let Lam : ℝ := w*U^(-((3:ℝ)/2))
  let M : ℝ := 3*w*U^(-((5:ℝ)/2))
  let L : ℝ := w^((11:ℝ)/30)*U^((7:ℝ)/20)
  have hr : 0 < r := stationaryBalancingRadius_pos hwp hUp
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hLam : 0 < Lam := by dsimp only [Lam]; positivity
  have hmuLam : mu ≤ Lam := by dsimp only [mu,Lam]; linarith only [hLam]
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hNwide : (N:ℝ)+1 ≤ 3*(w*U^(-((1:ℝ)/2))+1) := by linarith only [hN]
  have hNlog : (N:ℝ)+1 ≤ 3*w := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hU (by norm_num : -((1:ℝ)/2) ≤ 0)
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 3*w)
    nlinarith only [hm,hN]
  have hP := truncated_poisson_error_le_local_circle_scale hw hU N hNlog
  have hG := circle_total_guard_error_le hw hU hUw hwU
    (G := 4*Lam*r+2) (by rfl)
  have hF := circle_total_separated_error_le hw hU hUw hwU
    (K := 3) (M := (N:ℝ)+1) (by norm_num) hNwide
  have hden : mu*r ≤ Real.pi*(Lam*r) := by
    have hpi : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_right hmuLam hr.le
    have hp := mul_le_mul_of_nonneg_right hpi (mul_pos hLam hr).le
    nlinarith only [hm,hp]
  have hF' : ((N:ℝ)+1)/(Real.pi*(Lam*r)) ≤ 192*L := by
    have hdiv := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ (N:ℝ)+1)
      (mul_pos hmu hr) hden
    exact hdiv.trans (by norm_num only [mul_assoc] at hF; exact hF)
  have hstation := circle_total_stationary_error_le hw hU hUw hwU
    (K := 3) (M := (N:ℝ)+1) (by norm_num) hNwide
  have hone : 2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r)) ≤
      256*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) := by
    have hh := stationary_radius_error_le hwp hUp (q := mu) le_rfl
    convert hh using 1
    dsimp only [M,r,mu]
    ring
  have hstation' : ((N:ℝ)+1)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) ≤ 1536*L := by
    exact (mul_le_mul_of_nonneg_left hone (by positivity)).trans
      (by norm_num only [mul_assoc] at hstation; exact hstation)
  change ((2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1)+
    (4*Lam*r+2)*(4/Real.sqrt mu)+((N:ℝ)+1)/(Real.pi*(Lam*r))+
    ((N:ℝ)+1)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) ≤ 2320*L
  linarith only [hP,hG,hF',hstation']

end WaveTurbulence.NumberTheory
