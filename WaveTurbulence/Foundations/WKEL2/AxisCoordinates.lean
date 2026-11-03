/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisKernel
public import WaveTurbulence.Foundations.WKEL2.ResonantMeasure

/-!
# Cylindrical coordinates for the anisotropic M₁ kernel
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Measure-preserving cylindrical coordinates with a fixed transverse carrier. -/
@[expose] def axisSliceEquiv {ℓ : Mom d} (hℓ : ℓ ≠ 0) : ℝ × Mom (d - 1) ≃ᵐ Mom d :=
  ((MeasurableEquiv.refl ℝ).prodCongr (perpIsometry hℓ).symm.toMeasurableEquiv).trans
    (sliceEquiv hℓ)

theorem axisSliceEquiv_apply {ℓ : Mom d} (hℓ : ℓ ≠ 0) (z : ℝ × Mom (d - 1)) :
    axisSliceEquiv hℓ z = z.1 • unitVec ℓ + ((perpIsometry hℓ).symm z.2 : Mom d) := by
  rw [axisSliceEquiv, MeasurableEquiv.trans_apply, sliceEquiv_apply]
  rfl

theorem measurePreserving_axisSliceEquiv {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    MeasurePreserving (axisSliceEquiv hℓ) (volume.prod volume) volume :=
  (measurePreserving_sliceEquiv hℓ).comp
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (perpIsometry hℓ).symm.measurePreserving)

/-- Orthogonal projection recovers the transverse slice coordinate. -/
theorem perpPart_slice {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    perpPart ℓ (t • unitVec ℓ + (w : Mom d)) = w := by
  apply Subtype.ext
  rw [coe_perpPart, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_unitVec hℓ, one_pow,
    inner_unitVec_eq_zero_of_mem_perp, mul_one, add_zero]
  abel

/-- Anisotropic spatial kernel corresponding to the angular sine denominator. -/
@[expose] def anisotropicKernel (ℓ u : Mom d) : ℝ :=
  ‖u‖⁻¹ * ‖(perpPart ℓ u : Mom d)‖⁻¹

theorem anisotropicKernel_nonneg (ℓ u : Mom d) : 0 ≤ anisotropicKernel ℓ u := by
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _))

/-- The inverse norm is the negative half-power of its squared norm, including at zero. -/
theorem inv_norm_eq_rpow_sq (u : Mom d) : ‖u‖⁻¹ = (‖u‖ ^ 2) ^ (-(1 : ℝ) / 2) := by
  rw [← Real.rpow_natCast ‖u‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg_one]

/-- Identification of the physical and cylindrical kernels. -/
theorem anisotropicKernel_axisSlice {ℓ : Mom d} (hℓ : ℓ ≠ 0) (z : ℝ × Mom (d - 1)) :
    anisotropicKernel ℓ (axisSliceEquiv hℓ z) = axisKernel 1 z := by
  rw [axisSliceEquiv_apply, anisotropicKernel, perpPart_slice hℓ,
    inv_norm_eq_rpow_sq, norm_sq_smul_unitVec_add hℓ]
  simp only [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  rw [axisKernel, Real.rpow_neg_one]

end WaveTurbulence.WKEL2
