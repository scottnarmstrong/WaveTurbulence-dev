/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicField
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Quantitative Picard existence for bounded cubic fields

The lifespan scales as the inverse square of the initial norm. The zero
initial datum has the global zero solution and is treated separately.
-/

public section

noncomputable section

open Set Metric

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance picardNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance picardSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance picardNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance picardSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- An explicit positive local lifespan for nonzero cubic data. -/
@[expose] def cubicLifespan (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x : E) : ℝ :=
  (8 * (‖T‖ + 1) * ‖x‖ ^ 2)⁻¹

theorem cubicLifespan_pos (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) {x : E} (hx : x ≠ 0) :
    0 < cubicLifespan T x := by
  unfold cubicLifespan
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- The cubic field is uniformly Lipschitz on a ball about the initial point. -/
theorem cubicField_lipschitzOn_ball (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x₀ : E) :
    LipschitzOnWith (3 * ‖T‖₊ * (2 * ‖x₀‖₊) ^ 2) (cubicField T)
      (closedBall x₀ ‖x₀‖) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have Hx : ‖x‖ ≤ 2 * ‖x₀‖ := by
    have H := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hx)
    linarith only [H]
  have Hy : ‖y‖ ≤ 2 * ‖x₀‖ := by
    have H := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hy)
    linarith only [H]
  simpa only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow,
    coe_nnnorm] using norm_cubicField_sub_le T (by positivity) Hx Hy

/-- Picard's hypotheses with the scale-invariant explicit lifespan. -/
theorem cubicField_isPicardLindelof (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {x : E} (hx : x ≠ 0) :
    IsPicardLindelof (fun _ : ℝ => cubicField T)
      (⟨0, le_rfl, (cubicLifespan_pos T hx).le⟩ : Icc 0 (cubicLifespan T x)) x
      ‖x‖₊ 0 ((‖T‖₊ + 1) * (2 * ‖x‖₊) ^ 3)
      (3 * ‖T‖₊ * (2 * ‖x‖₊) ^ 2) := by
  apply IsPicardLindelof.of_time_independent
  · intro y hy
    have Hy : ‖y‖ ≤ 2 * ‖x‖ := by
      have H := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hy)
      simp only [coe_nnnorm] at H
      linarith only [H]
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_pow,
      NNReal.coe_ofNat, coe_nnnorm]
    apply (norm_cubicField_le T y).trans
    exact mul_le_mul (le_add_of_nonneg_right zero_le_one) (pow_le_pow_left₀ (norm_nonneg _) Hy 3)
      (by positivity) (by positivity)
  · exact cubicField_lipschitzOn_ball T x
  · simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_pow,
      NNReal.coe_ofNat, coe_nnnorm, sub_zero, NNReal.coe_zero,
      max_eq_left (cubicLifespan_pos T hx).le]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hT : ‖T‖ + 1 ≠ 0 := ne_of_gt (by positivity)
    unfold cubicLifespan
    apply le_of_eq
    field_simp
    ring

variable [CompleteSpace E]

/-- Quantitative local existence in any Banach space for a bounded cubic field. -/
theorem exists_cubic_solution (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {x : E} (hx : x ≠ 0) :
    ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc 0 (cubicLifespan T x),
        HasDerivWithinAt u (cubicField T (u t)) (Icc 0 (cubicLifespan T x)) t :=
  (cubicField_isPicardLindelof T hx).exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end WaveTurbulence.WKEL2
