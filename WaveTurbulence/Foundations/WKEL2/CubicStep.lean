/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicGlue

/-!
# A uniform continuation step for bounded cubic data
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance stepNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance stepSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance stepNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance stepSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- A positive lifespan uniform over a norm-bounded set of initial data. -/
@[expose] def cubicUniformStep (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (R : ℝ) : ℝ :=
  (8 * (‖T‖ + 1) * (R + 1) ^ 2)⁻¹

theorem cubicUniformStep_pos (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) {R : ℝ} (hR : 0 ≤ R) :
    0 < cubicUniformStep T R := by unfold cubicUniformStep; positivity

variable [CompleteSpace E]

/-- Picard existence with one lifespan valid for every datum in a fixed bounded ball. -/
theorem exists_cubic_solution_uniform (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {R : ℝ} (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t ∈ Icc 0 (cubicUniformStep T R),
      HasDerivWithinAt u (cubicField T (u t)) (Icc 0 (cubicUniformStep T R)) t := by
  by_cases hx₀ : x = 0
  · subst x
    exact ⟨fun _ => 0, rfl, fun t _ => cubic_zero_solution T _ t⟩
  obtain ⟨u, hu₀, hu⟩ := exists_cubic_solution T hx₀
  have hle : cubicUniformStep T R ≤ cubicLifespan T x := by
    unfold cubicUniformStep cubicLifespan
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (hx.trans (le_add_of_nonneg_right zero_le_one)) 2
  exact ⟨u, hu₀, fun t ht => (hu t ⟨ht.1, ht.2.trans hle⟩).mono
    (Icc_subset_Icc le_rfl hle)⟩

/-- A bounded endpoint permits extension by the uniform Picard step. -/
theorem extend_cubic_solution (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {R b c : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (hbc : b ≤ c)
    (hc : c ≤ b + cubicUniformStep T R) {u : ℝ → E}
    (hu : ∀ t ∈ Icc 0 b, HasDerivWithinAt u (cubicField T (u t)) (Icc 0 b) t)
    (hub : ‖u b‖ ≤ R) :
    ∃ w : ℝ → E, EqOn w u (Icc 0 b) ∧
      ∀ t ∈ Icc 0 c, HasDerivWithinAt w (cubicField T (w t)) (Icc 0 c) t := by
  obtain ⟨v, hv₀, hv⟩ := exists_cubic_solution_uniform T hR hub
  let g : ℝ → E := fun t => v (t - b)
  have hg : ∀ t ∈ Icc b c, HasDerivWithinAt g (cubicField T (g t)) (Icc b c) t := by
    intro t ht
    have hm : MapsTo (fun r : ℝ => r - b) (Icc b c) (Icc 0 (cubicUniformStep T R)) :=
      fun r hr => ⟨sub_nonneg.mpr hr.1, by linarith only [hr.2, hc]⟩
    have H := (hv (t - b) ⟨sub_nonneg.mpr ht.1, by linarith only [ht.2, hc]⟩).scomp t
      ((hasDerivAt_id t).sub_const b).hasDerivWithinAt (s := Icc b c)
      hm
    simpa only [one_smul, Function.comp_def, id_eq, g] using H
  have hmatch : u b = g b := by simp only [g, sub_self, hv₀]
  refine ⟨glueCurve b u g, fun t ht => ite_eq_left ht.2, ?_⟩
  exact hasDerivWithinAt_glueCurve T hb hbc hu hg hmatch

end WaveTurbulence.WKEL2
