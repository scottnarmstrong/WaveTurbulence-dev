/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.HyperplaneChart

/-!
# Radial invariance of the hyperplane chart

The measurable Householder chart depends only on the direction of a nonzero normal.
-/

public section

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Positive scaling does not change the normalized normal, including at zero. -/
theorem unitVec_pos_smul (a : Mom d) {r : ℝ} (hr : 0 < r) :
    unitVec (r • a) = unitVec a := by
  rw [unitVec, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv, smul_smul]
  rw [show r⁻¹ * ‖a‖⁻¹ * r = ‖a‖⁻¹ by
    calc
      _ = (r⁻¹ * r) * ‖a‖⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hr.ne', one_mul]]
  rfl

/-- The ambient reflection is constant on each positive ray of normals. -/
theorem normalReflection_pos_smul (e a : Mom d) {r : ℝ} (hr : 0 < r) :
    normalReflection e (r • a) = normalReflection e a := by
  ext x
  rw [normalReflection_apply, normalReflection_apply, unitVec_pos_smul a hr]

end WaveTurbulence.WKEL2
