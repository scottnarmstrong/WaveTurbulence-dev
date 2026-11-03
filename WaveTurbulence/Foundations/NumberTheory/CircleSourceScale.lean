/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Exact normalization of the circle source derivative scales

The shared source calculus uses powers of `R*U`. The quantitative transfer
uses `w=h*sqrt(R)`. These identities preserve the constants, including the
factor one eighth in the lower curvature.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem source_power_identity {R U : ℝ} (hR : 0 < R) (hU : 0 < U)
    (h : ℝ) (k : ℕ) (s : ℝ) :
    h*R^k*(R*U)^s = h*R^((k:ℝ)+s)*U^s := by
  rw [Real.mul_rpow hR.le hU.le,Real.rpow_add hR,Real.rpow_natCast]
  ring

/-- Exact source-frequency upper scale. -/
theorem circle_source_first_derivative_scale {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (h : ℝ) :
    h*R*(R*U)^(-((1:ℝ)/2)) = (h*Real.sqrt R)*U^(-((1:ℝ)/2)) := by
  have he := source_power_identity hR hU h 1 (-((1:ℝ)/2))
  norm_num only [pow_one,Nat.cast_one,show (1:ℝ)+(-(1/2)) = 1/2 by norm_num] at he
  simpa only [← Real.sqrt_eq_rpow] using he

/-- Exact upper curvature scale. -/
theorem circle_source_upper_curvature_scale {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (h : ℝ) :
    h*R^2*(R*U)^(-((3:ℝ)/2)) = (h*Real.sqrt R)*U^(-((3:ℝ)/2)) := by
  rw [source_power_identity hR hU]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)+(-(3/2)) = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow]

/-- Exact lower curvature scale, including its absolute factor. -/
theorem circle_source_lower_curvature_scale {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (h : ℝ) :
    h*R^2*(4*R*U)^(-((3:ℝ)/2)) = (h*Real.sqrt R)*U^(-((3:ℝ)/2))/8 := by
  have hfour : (4:ℝ)^(-((3:ℝ)/2)) = 1/8 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    have he : (4:ℝ)^((3:ℝ)/2) = 8 := by
      rw [show (3:ℝ)/2 = 1+1/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one,← Real.sqrt_eq_rpow]
      norm_num
    rw [he]
    norm_num
  rw [show (4:ℝ)*R*U = 4*(R*U) by ring,Real.mul_rpow (by norm_num) (mul_pos hR hU).le,hfour]
  calc
    _ = (h*R^2*(R*U)^(-((3:ℝ)/2)))/8 := by ring
    _ = _ := by rw [circle_source_upper_curvature_scale hR hU]

/-- Exact cubic-derivative scale. -/
theorem circle_source_third_derivative_scale {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (h : ℝ) :
    3*h*R^3*(R*U)^(-((5:ℝ)/2)) = 3*(h*Real.sqrt R)*U^(-((5:ℝ)/2)) := by
  rw [source_power_identity hR hU]
  norm_num only [Nat.cast_ofNat,show (3:ℝ)+(-(5/2)) = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow]
  ring

/-- The scalar local powers are exactly the frequency, radius and endpoint
powers used by the final circle transfer. -/
theorem circle_source_local_power_identity {R : ℝ} (hR : 0 < R) {h : ℝ} (hh : 0 < h) (U : ℝ) :
    (h*Real.sqrt R)^((11:ℝ)/30)*U^((7:ℝ)/20) =
      h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20) := by
  rw [Real.mul_rpow hh.le (Real.sqrt_nonneg R),Real.sqrt_eq_rpow,← Real.rpow_mul hR.le]
  norm_num

end WaveTurbulence.NumberTheory
