/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VdCB.CircleBPreEstimate
public import WaveTurbulence.Foundations.NumberTheory.CircleOptimizedBError
public import WaveTurbulence.Foundations.NumberTheory.CircleSourceScale
import Mathlib.Tactic

/-!
# The actual circle source B estimate after optimizing both free error parameters.
-/

public section

open Set
namespace WaveTurbulence.NumberTheory

theorem circle_B_error_at_balanced_radius_le {R h U : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hU : 1 ≤ U) (hw : 1 ≤ h*Real.sqrt R)
    (hUw : U ≤ (h*Real.sqrt R)^2) (hwU : h*Real.sqrt R ≤ U^2) :
    VdCB.circleBError R h U (stationaryBalancingRadius (h*Real.sqrt R) U)
      (Real.sqrt (VdCB.circleCurvatureLower R h U)) ≤ 4000*VdCB.circleBScale R h U := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  simp only [VdCB.circleBError,VdCB.circleCurvatureLower,VdCB.circleCurvatureUpper,
    VdCB.circleThirdScale,circle_source_lower_curvature_scale hR hUp,
    circle_source_upper_curvature_scale hR hUp,circle_source_third_derivative_scale hR hUp]
  rw [VdCB.circleBScale,← circle_source_local_power_identity hR hh U]
  exact circle_optimized_B_error_le hw hU hUw hwU

theorem norm_sum_circleColumnPhase_le_optimized_BScale {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 0 < h) (hw : 1 ≤ h*Real.sqrt R)
    (hUw : U ≤ (h*Real.sqrt R)^2) (hwU : h*Real.sqrt R ≤ U^2)
    {a b : ℕ} (hab : a ≤ b) (ha : R+c-2*U ≤ a) (hb : (b:ℝ) ≤ R+c-U)
    (haOct : R+c-R*(1-1/Real.sqrt 2) ≤ a)
    (hinner : (a:ℝ)+stationaryBalancingRadius (h*Real.sqrt R) U ≤
      b-stationaryBalancingRadius (h*Real.sqrt R) U) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ ≤
      154618826665*VdCB.circleBScale R h U := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  have hwp : 0 < h*Real.sqrt R := zero_lt_one.trans_le hw
  have hr := stationaryBalancingRadius_pos hwp hUp
  have ht : 0 < Real.sqrt (VdCB.circleCurvatureLower R h U) := by
    apply Real.sqrt_pos.mpr
    unfold VdCB.circleCurvatureLower
    positivity
  have hsum := VdCB.norm_sum_circleColumnPhase_le_BScale_add_error hU hUR hh hr ht hab ha hb haOct hinner
  have herr := circle_B_error_at_balanced_radius_le hR hh hU hw hUw hwU
  linarith only [hsum,herr]

end WaveTurbulence.NumberTheory
