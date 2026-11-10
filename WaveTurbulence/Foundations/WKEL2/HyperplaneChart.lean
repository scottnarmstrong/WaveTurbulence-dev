/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Hyperplane
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# A measurable trivialization of hyperplane volume

Use reflection perpendicular to `e - unitVec a` to identify a fixed reference
hyperplane with `a`-perp. The ambient reflection is measurable jointly in its
normal and its argument, including the exceptional direction where it is the
identity. No continuity at that direction is asserted.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Householder reflection taking a reference unit vector to the normalized normal. -/
@[expose] noncomputable def normalReflection (e a : Mom d) : Mom d ≃ₗᵢ[ℝ] Mom d :=
  (ℝ ∙ (e - unitVec a))ᗮ.reflection

/-- Explicit reflection formula; totalized inversion makes this measurable everywhere. -/
theorem normalReflection_apply (e a x : Mom d) :
    normalReflection e a x =
      x - (2 * (⟪e - unitVec a, x⟫_ℝ / ‖e - unitVec a‖ ^ 2)) • (e - unitVec a) := by
  rw [normalReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub]
  simp only [two_smul, two_mul, add_smul]

/-- Measurability of the normalized normal, with value zero at zero. -/
theorem measurable_unitVec : Measurable (unitVec : Mom d → Mom d) :=
  measurable_norm.inv.smul measurable_id

/-- Joint measurability of the Householder chart. -/
theorem measurable_normalReflection (e : Mom d) :
    Measurable (fun p : Mom d × Mom d => normalReflection e p.1 p.2) := by
  simp_rw [normalReflection_apply]
  have hn : Measurable (fun p : Mom d × Mom d => e - unitVec p.1) :=
    measurable_const.sub (measurable_unitVec.comp measurable_fst)
  exact measurable_snd.sub ((measurable_const.mul
    ((hn.inner measurable_snd).div (hn.norm.pow_const 2))).smul hn)

/-- The reference unit vector is sent to the normalized nonzero normal. -/
theorem normalReflection_reference {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0) :
    normalReflection e a e = unitVec a :=
  Submodule.reflection_sub (he.trans (norm_unitVec ha).symm)

/-- Membership in the moving hyperplane in fixed coordinates. -/
theorem normalReflection_mem_perp_iff {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0)
    (x : Mom d) :
    normalReflection e a x ∈ (ℝ ∙ a)ᗮ ↔ x ∈ (ℝ ∙ e)ᗮ := by
  rw [← span_unitVec ha]
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← normalReflection_reference he ha,
    (normalReflection e a).inner_map_map]

/-- The image of the fixed hyperplane is precisely the moving hyperplane. -/
theorem map_perp_normalReflection {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0) :
    ((ℝ ∙ e)ᗮ).map (normalReflection e a).toLinearMap = (ℝ ∙ a)ᗮ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (normalReflection_mem_perp_iff he ha x).mpr hx
  · intro hy
    refine ⟨normalReflection e a y, ?_, ?_⟩
    · apply (normalReflection_mem_perp_iff he ha _).mp
      simpa only [normalReflection, Submodule.reflection_reflection] using hy
    · exact Submodule.reflection_reflection _ _

/-- Linear isometric identification of a fixed hyperplane with a moving one. -/
@[expose] noncomputable def hyperplaneChart {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0) :
    ↥(ℝ ∙ e)ᗮ ≃ₗᵢ[ℝ] ↥(ℝ ∙ a)ᗮ :=
  (LinearIsometryEquiv.submoduleMap (ℝ ∙ e)ᗮ (normalReflection e a)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_perp_normalReflection he ha))

/-- The chart's ambient value is the explicit measurable reflection. -/
theorem coe_hyperplaneChart {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0)
    (w : ↥(ℝ ∙ e)ᗮ) :
    (hyperplaneChart he ha w : Mom d) = normalReflection e a w := rfl

/-- Hyperplane volume is transported by the chart. -/
theorem measurePreserving_hyperplaneChart {e a : Mom d} (he : ‖e‖ = 1) (ha : a ≠ 0) :
    MeasurePreserving (hyperplaneChart he ha) :=
  (hyperplaneChart he ha).measurePreserving

end WaveTurbulence.WKEL2
