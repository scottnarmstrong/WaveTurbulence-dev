/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.StationaryErrorBounds
import Mathlib.Tactic

/-!
# Frequency-summed stationary and nonstationary circle errors

The actual balancing radius gives an explicit error after summing over a
frequency interval of the source derivative's natural width. Both the
stationary remainder and the separated-frequency integral cost fit the
improved local powers. These are scalar estimates, not a B identity.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Exact multiplication by the natural dual-frequency width. -/
theorem circle_frequency_width_mul_stationary_scale {w U : ℝ}
    (hw : 0 < w) (hU : 0 < U) :
    (w*U^(-((1:ℝ)/2)))*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) =
      w^((2:ℝ)/5)*U^((1:ℝ)/5) := by
  calc
    _ = (w*w^(-((3:ℝ)/5)))*(U^(-((1:ℝ)/2))*U^((7:ℝ)/10)) := by ring
    _ = _ := by
      have he := Real.rpow_add hw (1:ℝ) (-((3:ℝ)/5))
      norm_num only [Real.rpow_one,show (1:ℝ)+(-(3/5)) = 2/5 by norm_num] at he
      rw [← he,← Real.rpow_add hU]
      norm_num

/-- The frequency count times one stationary remainder is controlled with
an explicit absolute constant in the complementary source range. -/
theorem circle_frequency_count_mul_stationary_scale_le {w U : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2) :
    (w*U^(-((1:ℝ)/2))+1)*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) ≤
      2*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hsqrt : U^((1:ℝ)/2) ≤ w := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨hwp.le,hUw⟩
  have h1 := rpow_mul_le_of_upper_scale hU hwp (u := 2)
    (a := (2:ℝ)/5) (b := (1:ℝ)/5) (c := (11:ℝ)/30) (d := (7:ℝ)/20)
    (by simpa only [Real.rpow_two] using hwU) (by norm_num) (by norm_num)
  have h2 := rpow_mul_le_of_lower_scale hU hwp hsqrt
    (a := -((3:ℝ)/5)) (b := (7:ℝ)/10) (c := (11:ℝ)/30) (d := (7:ℝ)/20)
    (by norm_num) (by norm_num)
  rw [add_mul,one_mul,circle_frequency_width_mul_stationary_scale hwp hUp]
  linarith only [h1,h2]

/-- Summing the explicit stationary error over at most a fixed multiple of
the natural frequency width still has the desired local powers. -/
theorem circle_total_stationary_error_le {w U K M : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2)
    (hK : 0 ≤ K) (hM : M ≤ K*(w*U^(-((1:ℝ)/2))+1)) :
    M*(256*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) ≤
      (512*K)*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hscale := circle_frequency_count_mul_stationary_scale_le hw hU hUw hwU
  have hE : 0 ≤ w^(-((3:ℝ)/5))*U^((7:ℝ)/10) := by positivity
  calc
    _ ≤ (K*(w*U^(-((1:ℝ)/2))+1))*(256*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) :=
      mul_le_mul_of_nonneg_right hM (by positivity)
    _ = (256*K)*((w*U^(-((1:ℝ)/2))+1)*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) := by ring
    _ ≤ (256*K)*(2*(w^((11:ℝ)/30)*U^((7:ℝ)/20))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

/-- The full separated-frequency integral cost at separation `mu*r`,
without any logarithmic estimate, is already small enough. -/
theorem circle_total_separated_error_le {w U K M : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2)
    (hK : 0 ≤ K) (hM : M ≤ K*(w*U^(-((1:ℝ)/2))+1)) :
    M/((w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U) ≤
      (64*K)*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have heq : M/((w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U) =
      M*(32*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) := by
    rw [div_eq_mul_one_div,stationary_radius_tail_term hwp hUp]
  rw [heq]
  have hscale := circle_frequency_count_mul_stationary_scale_le hw hU hUw hwU
  calc
    _ ≤ (K*(w*U^(-((1:ℝ)/2))+1))*(32*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) :=
      mul_le_mul_of_nonneg_right hM (by positivity)
    _ = (32*K)*((w*U^(-((1:ℝ)/2))+1)*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10))) := by ring
    _ ≤ (32*K)*(2*(w^((11:ℝ)/30)*U^((7:ℝ)/20))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end WaveTurbulence.NumberTheory
