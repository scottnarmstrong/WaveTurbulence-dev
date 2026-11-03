/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CirclePoissonErrorScale
public import WaveTurbulence.Foundations.NumberTheory.CircleGuardErrorScale
public import WaveTurbulence.Foundations.NumberTheory.CircleSummedStationaryScale
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Optimizing the explicit direct-circle B-process error

This is the numeric error expression of the shared direct-circle
pre-estimate, with balanced spatial radius and threshold sqrt(curvature).
Every term is controlled at the improved local circle powers.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The explicit direct-circle B error, after choosing both free parameters,
is uniformly bounded by an absolute multiple of the local circle power. -/
theorem circle_optimized_B_error_le {w U : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U)
    (hUw : U ≤ w^2) (hwU : w ≤ U^2) :
    let r := stationaryBalancingRadius w U
    let mu := w*U^(-((3:ℝ)/2))/8
    let Lam := w*U^(-((3:ℝ)/2))
    let M := 3*w*U^(-((5:ℝ)/2))
    ((2+6*Real.log (Lam*U+3))/(2*Real.pi)+1)+
      2*(Lam*r+3)*(2*Real.sqrt mu/mu+2/(Real.pi*Real.sqrt mu))+
      (Lam*U+3)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) ≤
      4000*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  let r := stationaryBalancingRadius w U
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  let Lam : ℝ := w*U^(-((3:ℝ)/2))
  let M : ℝ := 3*w*U^(-((5:ℝ)/2))
  let L : ℝ := w^((11:ℝ)/30)*U^((7:ℝ)/20)
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hr : 0 < r := stationaryBalancingRadius_pos hwp hUp
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hLam : 0 < Lam := by dsimp only [Lam]; positivity
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hw (by norm_num)) (Real.one_le_rpow hU (by norm_num))
  have hpi : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have hwidth : Lam*U = w*U^(-((1:ℝ)/2)) := by
    dsimp only [Lam]
    have he := Real.rpow_add hUp (-((3:ℝ)/2)) 1
    norm_num only [Real.rpow_one,show (-((3:ℝ)/2))+1 = -(1/2) by norm_num] at he
    rw [mul_assoc,← he]
  have hQw : Lam*U+3 ≤ 4*w := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hU (by norm_num : -((1:ℝ)/2) ≤ 0)
    have hm := mul_le_mul_of_nonneg_left hp hwp.le
    rw [hwidth]
    linarith only [hm,hw]
  have hlog := log_le_local_circle_scale_four hw hU
    (show 0 ≤ Lam*U+3 by positivity) hQw
  have hnum : 0 ≤ 2+6*Real.log (Lam*U+3) := by
    have hh : 0 ≤ Real.log (Lam*U+3) := Real.log_nonneg (by nlinarith only [mul_pos hLam hUp])
    positivity
  have hdiv := div_le_self hnum (show 1 ≤ 2*Real.pi by linarith only [hpi])
  have hP : (2+6*Real.log (Lam*U+3))/(2*Real.pi)+1 ≤ 100*L := by
    linarith only [hdiv,hlog,hL]
  have hquot : Real.sqrt mu/mu = 1/Real.sqrt mu := by
    apply (div_eq_div_iff hmu.ne' hs.ne').mpr
    simpa only [one_mul] using Real.mul_self_sqrt hmu.le
  have htail : 2/(Real.pi*Real.sqrt mu) ≤ 2/Real.sqrt mu :=
    div_le_div_of_nonneg_left (by norm_num) hs
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hs.le)
  have hG0 := circle_total_guard_error_le hw hU hUw hwU
    (G := 4*Lam*r+2) (by rfl)
  have hG : 2*(Lam*r+3)*(2*Real.sqrt mu/mu+2/(Real.pi*Real.sqrt mu)) ≤ 1536*L := by
    have hinner : 2*Real.sqrt mu/mu+2/(Real.pi*Real.sqrt mu) ≤ 4/Real.sqrt mu := by
      rw [mul_div_assoc,hquot]
      calc
        _ ≤ 2*(1/Real.sqrt mu)+2/Real.sqrt mu := add_le_add le_rfl htail
        _ = _ := by ring
    calc
      _ ≤ (2*(Lam*r+3))*(4/Real.sqrt mu) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ (3*(4*Lam*r+2))*(4/Real.sqrt mu) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [mul_pos hLam hr]) (by positivity)
      _ = 3*((4*Lam*r+2)*(4/Real.sqrt mu)) := by ring
      _ ≤ _ := by linarith only [hG0]
  have hone : 2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r)) ≤
      256*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) := by
    have hh := stationary_radius_error_le hwp hUp (q := mu) le_rfl
    convert hh using 1
    dsimp only [M,r,mu]
    ring
  have hcount : Lam*U+3 ≤ 3*(w*U^(-((1:ℝ)/2))+1) := by
    rw [hwidth]
    have hh : 0 ≤ w*U^(-((1:ℝ)/2)) := by positivity
    linarith only [hh]
  have htotal := circle_total_stationary_error_le hw hU hUw hwU (K := 3)
    (M := Lam*U+3) (by norm_num) hcount
  have hS : (Lam*U+3)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) ≤ 1536*L := by
    exact (mul_le_mul_of_nonneg_left hone (by positivity)).trans
      (by norm_num only [mul_assoc] at htotal; exact htotal)
  change ((2+6*Real.log (Lam*U+3))/(2*Real.pi)+1)+
    2*(Lam*r+3)*(2*Real.sqrt mu/mu+2/(Real.pi*Real.sqrt mu))+
    (Lam*U+3)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) ≤ 4000*L
  linarith only [hP,hG,hS,hL]

end WaveTurbulence.NumberTheory
