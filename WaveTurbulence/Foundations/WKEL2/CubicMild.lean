/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicField
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differential and mild solutions of bounded cubic Banach equations
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance mildNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance mildSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance mildNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance mildSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- Duhamel's equation in the complete weighted model. -/
@[expose] def IsCubicMildSolution (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (x₀ : E) (b : ℝ) (u : ℝ → E) : Prop :=
  ContinuousOn u (Icc 0 b) ∧ ∀ t ∈ Icc 0 b,
    u t = x₀ + ∫ r in (0 : ℝ)..t, cubicField T (u r)

/-- Every differential solution satisfies the actual Bochner Duhamel equation. -/
theorem cubic_solution_isMild [CompleteSpace E]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) {b : ℝ} {u : ℝ → E}
    (hu : ∀ t ∈ Icc 0 b, HasDerivWithinAt u (cubicField T (u t)) (Icc 0 b) t) :
    IsCubicMildSolution T (u 0) b u := by
  have hc : ContinuousOn u (Icc 0 b) := fun t ht => (hu t ht).continuousWithinAt
  refine ⟨hc, fun t ht => ?_⟩
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hv : ContinuousOn (fun r => cubicField T (u r)) (Icc 0 t) :=
    (continuous_cubicField T).comp_continuousOn (hc.mono hsub)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hc.mono hsub)
    (fun r hr => ((hu r ⟨hr.1.le, (hr.2.trans_le ht.2).le⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))).hasDerivWithinAt (s := Ioi r))
    (hv.intervalIntegrable_of_Icc ht.1)
  rw [H]
  abel

/-- The continuous mild equation differentiates on the closed interval, including its endpoints. -/
theorem IsCubicMildSolution.hasDerivWithinAt [CompleteSpace E]
    {T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E} {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : IsCubicMildSolution T x₀ b u) (t : ℝ) (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt u (cubicField T (u t)) (Icc 0 b) t := by
  have hv : ContinuousOn (fun r => cubicField T (u r)) (Icc 0 b) :=
    (continuous_cubicField T).comp_continuousOn hu.1
  have hi : IntervalIntegrable (fun r => cubicField T (u r)) volume 0 t := (hv.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  let : Fact (t ∈ Icc 0 b) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 b) (t := Icc 0 b) hi
    (hv.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hv t ht)
  exact (hd.const_add x₀).congr_of_mem (fun r hr => hu.2 r hr) ht

end WaveTurbulence.WKEL2
