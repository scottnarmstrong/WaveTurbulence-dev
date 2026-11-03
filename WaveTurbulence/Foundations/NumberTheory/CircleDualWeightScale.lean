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
# Scalar exponents after the circle dual amplitude

These are exact scalar identities for the dual A-scale and its curvature
weight. They assert no stationary-phase formula or B-process estimate.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Exact product of the circle curvature weight and a dual power bound. -/
theorem circle_dual_weight_scale_identity {R h Y : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hY : 0 < Y) (kappa lambda : ℝ) :
    (Real.sqrt R*h/Y^((3:ℝ)/2))*((R*h^2/Y^2)^kappa*Y^lambda) =
      R^(kappa+1/2)*h^(2*kappa+1)*Y^(lambda-2*kappa-3/2) := by
  rw [Real.sqrt_eq_rpow,Real.div_rpow (by positivity : 0 ≤ R*h^2) (sq_nonneg Y),
    Real.mul_rpow hR.le (sq_nonneg h),← Real.rpow_natCast_mul hh.le 2,
    ← Real.rpow_natCast_mul hY.le 2]
  norm_num only [Nat.cast_ofNat]
  have he : lambda-2*kappa-3/2 = (lambda+(-(2*kappa)))+(-(3/2:ℝ)) := by ring
  rw [he,Real.rpow_add hY,Real.rpow_add hY,Real.rpow_neg hY.le,Real.rpow_neg hY.le,
    Real.rpow_add hR,Real.rpow_add hh,Real.rpow_one]
  ring

/-- The `(1/30,26/30)` dual A-scale has the precise weighted powers. -/
theorem circle_dual_weight_fifth_scale_identity {R h Y : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hY : 0 < Y) :
    (Real.sqrt R*h/Y^((3:ℝ)/2))*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)) =
      R^((8:ℝ)/15)*h^((16:ℝ)/15)*Y^(-((7:ℝ)/10)) := by
  have he := circle_dual_weight_scale_identity hR hh hY ((1:ℝ)/30) ((26:ℝ)/30)
  norm_num at he
  norm_num only [show (26:ℝ)/30 = 13/15 by norm_num]
  exact he

/-- Substituting the endpoint-distance dual scale produces precisely the
local powers used by the proved endpoint-to-circle transfer. -/
theorem circle_dual_endpoint_scale_identity {R h U : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hU : 0 < U) :
    R^((8:ℝ)/15)*h^((16:ℝ)/15)*(h*Real.sqrt (R/U))^(-((7:ℝ)/10)) =
      h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20) := by
  rw [Real.mul_rpow hh.le (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
    ← Real.rpow_mul (div_pos hR hU).le]
  norm_num only [show ((1:ℝ)/2)*(-(7/10)) = -(7/20) by norm_num]
  rw [Real.div_rpow hR.le hU.le,Real.rpow_neg hU.le,div_inv_eq_mul]
  have he : R^((8:ℝ)/15)*h^((16:ℝ)/15)*
      (h^(-((7:ℝ)/10))*(R^(-((7:ℝ)/20))*U^((7:ℝ)/20))) =
      (R^((8:ℝ)/15)*R^(-((7:ℝ)/20)))*
        (h^((16:ℝ)/15)*h^(-((7:ℝ)/10)))*U^((7:ℝ)/20) := by ring
  rw [he,← Real.rpow_add hR,← Real.rpow_add hh]
  norm_num
  exact Or.inl (mul_comm _ _)

/-- A dual block whose scale is comparable to the endpoint-distance scale
has exactly the local powers consumed by the circle transfer. This is a
scalar inequality and does not assume a B-process formula. -/
theorem circle_dual_weight_endpoint_bound {R h Y U : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hY : 0 < Y) (hU : 0 < U)
    (hscale : (h*Real.sqrt (R/U))/4 ≤ Y) :
    (Real.sqrt R*h/Y^((3:ℝ)/2))*((R*h^2/Y^2)^((1:ℝ)/30)*Y^((26:ℝ)/30)) ≤
      4*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  let B : ℝ := h*Real.sqrt (R/U)
  have hB : 0 < B := mul_pos hh (Real.sqrt_pos.mpr (div_pos hR hU))
  have hpow : Y^(-((7:ℝ)/10)) ≤ 4*B^(-((7:ℝ)/10)) := by
    calc
      _ ≤ (B/4)^(-((7:ℝ)/10)) := Real.rpow_le_rpow_of_nonpos (by positivity) hscale (by norm_num)
      _ = (4:ℝ)^((7:ℝ)/10)*B^(-((7:ℝ)/10)) := by
        rw [Real.div_rpow hB.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),div_inv_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (7:ℝ)/10 ≤ 1))
        (Real.rpow_nonneg hB.le _)
  calc
    _ = R^((8:ℝ)/15)*h^((16:ℝ)/15)*Y^(-((7:ℝ)/10)) :=
      circle_dual_weight_fifth_scale_identity hR hh hY
    _ ≤ R^((8:ℝ)/15)*h^((16:ℝ)/15)*(4*B^(-((7:ℝ)/10))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 4*(R^((8:ℝ)/15)*h^((16:ℝ)/15)*B^(-((7:ℝ)/10))) := by ring
    _ = _ := by rw [circle_dual_endpoint_scale_identity hR hh hU]

end WaveTurbulence.NumberTheory
