/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicPicard
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniqueness for bounded cubic Banach fields

Every continuous trajectory on a compact interval is bounded. The explicit
local Lipschitz estimate therefore gives uniqueness on the whole interval.
-/

public section

noncomputable section

open Set Metric

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance uniquenessNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance uniquenessSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance uniquenessNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance uniquenessSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- Cubic ODE solutions with the same initial value agree throughout a closed interval. -/
theorem cubic_solution_unique (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {a b : ℝ} {f g : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (cubicField T (f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (cubicField T (g t)) (Icc a b) t)
    (h₀ : f a = g a) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  obtain ⟨Rf, hRf⟩ := (isCompact_Icc.image_of_continuousOn hfc).isBounded.exists_norm_le
  obtain ⟨Rg, hRg⟩ := (isCompact_Icc.image_of_continuousOn hgc).isBounded.exists_norm_le
  let R := max 0 (max Rf Rg)
  have hR : 0 ≤ R := le_max_left _ _
  have hRfR : Rf ≤ R := (le_max_left Rf Rg).trans (le_max_right _ _)
  have hRgR : Rg ≤ R := (le_max_right Rf Rg).trans (le_max_right _ _)
  have hfb : ∀ t ∈ Icc a b, ‖f t‖ ≤ R :=
    fun t ht => (hRf _ (mem_image_of_mem _ ht)).trans hRfR
  have hgb : ∀ t ∈ Icc a b, ‖g t‖ ≤ R :=
    fun t ht => (hRg _ (mem_image_of_mem _ ht)).trans hRgR
  have hLip : LipschitzOnWith (Real.toNNReal (3 * ‖T‖ * R ^ 2)) (cubicField T)
      {x | ‖x‖ ≤ R} := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    simpa only [dist_eq_norm] using norm_cubicField_sub_le T hR hx hy
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => {x | ‖x‖ ≤ R})
    (fun _ _ => hLip) hfc ?_ (fun t ht => hfb t (Ico_subset_Icc_self ht)) hgc ?_
    (fun t ht => hgb t (Ico_subset_Icc_self ht)) h₀
  · intro t ht
    exact (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    exact (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- The zero initial datum has a global zero solution. -/
theorem cubic_zero_solution (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (S : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun _ : ℝ => (0 : E)) (cubicField T 0) S t := by
  simpa only [cubicField, map_zero, zero_apply] using
    (hasDerivAt_const t (0 : E)).hasDerivWithinAt (s := S)

end WaveTurbulence.WKEL2
