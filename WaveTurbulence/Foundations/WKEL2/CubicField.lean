/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Cubic fields associated to bounded trilinear maps

The norm and local Lipschitz bounds here are the quantitative inputs for
Picard local existence in the exact weighted L² Banach space.
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance normedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance spaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance normedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance spaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The diagonal cubic vector field of a continuous trilinear map. -/
@[expose] def cubicField (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x : E) : E := T x x x

/-- The curried trilinear operator norm controls every value. -/
theorem norm_trilinear_apply_le (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x y z : E) :
    ‖T x y z‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ * ‖z‖ := by
  exact (T x).le_opNorm₂ y z |>.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg y)) (norm_nonneg z))

/-- Cubic growth of the collision field. -/
theorem norm_cubicField_le (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x : E) :
    ‖cubicField T x‖ ≤ ‖T‖ * ‖x‖ ^ 3 := by
  simpa only [cubicField, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using norm_trilinear_apply_le T x x x

/-- Telescoping in the three slots gives the cubic difference identity. -/
theorem cubicField_sub (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x y : E) :
    cubicField T x - cubicField T y =
      T (x - y) x x + T y (x - y) x + T y y (x - y) := by
  simp only [cubicField, map_sub, sub_apply]
  abel

/-- Uniform local Lipschitz estimate on any norm-bounded set. -/
theorem norm_cubicField_sub_le (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {R : ℝ} (hR : 0 ≤ R) {x y : E} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖cubicField T x - cubicField T y‖ ≤ (3 * ‖T‖ * R ^ 2) * ‖x - y‖ := by
  rw [cubicField_sub]
  have H₁ : ‖T (x - y) x x‖ ≤ ‖T‖ * ‖x - y‖ * R * R :=
    (norm_trilinear_apply_le T _ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hx (mul_nonneg (norm_nonneg T) (norm_nonneg _)))
        hx (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg T) (norm_nonneg _)) hR))
  have H₂ : ‖T y (x - y) x‖ ≤ ‖T‖ * R * ‖x - y‖ * R := by
    apply (norm_trilinear_apply_le T _ _ _).trans
    gcongr
  have H₃ : ‖T y y (x - y)‖ ≤ ‖T‖ * R * R * ‖x - y‖ := by
    apply (norm_trilinear_apply_le T _ _ _).trans
    gcongr
  calc
    _ ≤ (‖T (x - y) x x‖ + ‖T y (x - y) x‖) + ‖T y y (x - y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖T‖ * ‖x - y‖ * R * R + ‖T‖ * R * ‖x - y‖ * R) +
        ‖T‖ * R * R * ‖x - y‖ := add_le_add (add_le_add H₁ H₂) H₃
    _ = _ := by ring

end WaveTurbulence.WKEL2
