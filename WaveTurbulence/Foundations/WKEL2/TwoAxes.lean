/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CodimTwoSlice
public import WaveTurbulence.Foundations.WKEL2.SineKernel
public import WaveTurbulence.Foundations.WKEL2.SphereNoAtoms

/-!
# Successive slicing coordinates adapted to two directions
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The second direction projected into coordinates perpendicular to the first. -/
@[expose] def transverseAxis {θ : Mom d} (hθ : θ ≠ 0) (v : Mom d) : Mom (d - 1) :=
  perpIsometry hθ (perpPart θ v)

/-- The transverse axis length is the sine Jacobian for unit directions. -/
theorem inv_norm_transverseAxis {θ : Mom d} (hθ : θ ≠ 0) (v : Mom d) :
    ‖transverseAxis hθ v‖⁻¹ = angularSineInv θ v := by
  rw [transverseAxis, LinearIsometryEquiv.norm_map]
  rfl

/-- Pairing against a transverse slice is pairing against the transverse axis. -/
theorem inner_perp_coordinates {θ : Mom d} (hθ : θ ≠ 0) (v : Mom d) (y : Mom (d - 1)) :
    ⟪v, ((perpIsometry hθ).symm y : Mom d)⟫_ℝ = ⟪transverseAxis hθ v, y⟫_ℝ := by
  have h := (perpIsometry hθ).inner_map_map (perpPart θ v) ((perpIsometry hθ).symm y)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [transverseAxis, h]
  change ⟪v, ((perpIsometry hθ).symm y : Mom d)⟫_ℝ =
    ⟪(perpPart θ v : Mom d), ((perpIsometry hθ).symm y : Mom d)⟫_ℝ
  rw [coe_perpPart, inner_sub_left, inner_smul_left, inner_unitVec_eq_zero_of_mem_perp,
    mul_zero, sub_zero]

/-- Volume coordinates obtained by two successive orthogonal slices. -/
@[expose] def twoAxisSliceEquiv {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) :
    ℝ × (ℝ × Mom (d - 1 - 1)) ≃ᵐ Mom d :=
  ((MeasurableEquiv.refl ℝ).prodCongr (axisSliceEquiv hη)).trans (axisSliceEquiv hθ)

theorem twoAxisSliceEquiv_apply {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) (p : ℝ × (ℝ × Mom (d - 1 - 1))) :
    twoAxisSliceEquiv hθ hη p = codimTwoSlice hθ hη p.1 p.2.1 p.2.2 := rfl

theorem measurePreserving_twoAxisSliceEquiv {θ : Mom d} (hθ : θ ≠ 0)
    {η : Mom (d - 1)} (hη : η ≠ 0) :
    MeasurePreserving (twoAxisSliceEquiv hθ hη) (volume.prod (volume.prod volume)) volume :=
  (measurePreserving_axisSliceEquiv hθ).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (measurePreserving_axisSliceEquiv hη))

/-- The first scalar slice coordinate is the inner product with the unit axis. -/
theorem inner_unit_axisSlice {θ : Mom d} (hθ : θ ≠ 0) (t : ℝ) (y : Mom (d - 1)) :
    ⟪unitVec θ, axisSliceEquiv hθ (t, y)⟫_ℝ = t := by
  rw [axisSliceEquiv_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_unitVec hθ, one_pow,
    inner_unitVec_eq_zero_of_mem_perp, mul_one, add_zero]

/-- The second scalar pairing is an affine shear of the orthogonal coordinates. -/
theorem inner_codimTwoSlice {θ v : Mom d} (hθ : θ ≠ 0)
    (hη : transverseAxis hθ v ≠ 0) (t u : ℝ) (z : Mom (d - 1 - 1)) :
    ⟪v, codimTwoSlice hθ hη t u z⟫_ℝ =
      t * ⟪v, unitVec θ⟫_ℝ + ‖transverseAxis hθ v‖ * u := by
  rw [codimTwoSlice, axisSliceEquiv_apply, inner_add_right, inner_smul_right,
    inner_perp_coordinates]
  have h := inner_unit_axisSlice hη u z
  rw [unitVec, inner_smul_left] at h
  have hnorm : ‖transverseAxis hθ v‖ ≠ 0 := norm_ne_zero_iff.mpr hη
  simp only [starRingEnd_apply, star_trivial] at h
  field_simp [hnorm] at h
  linear_combination h

end WaveTurbulence.WKEL2
