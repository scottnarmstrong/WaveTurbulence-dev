/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisCoordinates

/-!
# Homogeneity of the anisotropic kernel and its angular factor
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Orthogonal projection onto a fixed hyperplane commutes with real scaling. -/
theorem perpPart_smul (ℓ u : Mom d) (r : ℝ) : perpPart ℓ (r • u) = r • perpPart ℓ u := by
  apply Subtype.ext
  simp only [coe_perpPart, Submodule.coe_smul, inner_smul_right, smul_sub, smul_smul]

/-- The angular sine denominator on unit vectors, with inverse zero totalized to zero. -/
@[expose] def angularSineInv (ℓ v : Mom d) : ℝ := ‖(perpPart ℓ v : Mom d)‖⁻¹

theorem angularSineInv_nonneg (ℓ v : Mom d) : 0 ≤ angularSineInv ℓ v :=
  inv_nonneg.mpr (norm_nonneg _)

theorem measurable_angularSineInv (ℓ : Mom d) : Measurable (angularSineInv ℓ) := by
  have hc : Continuous (fun v : Mom d => (perpPart ℓ v : Mom d)) := by
    simp only [coe_perpPart]
    fun_prop
  exact hc.measurable.norm.inv

/-- Homogeneity of degree minus two. -/
theorem anisotropicKernel_pos_smul (ℓ u : Mom d) {r : ℝ} (hr : 0 < r) :
    anisotropicKernel ℓ (r • u) = r⁻¹ * r⁻¹ * anisotropicKernel ℓ u := by
  simp only [anisotropicKernel, perpPart_smul, Submodule.coe_smul, norm_smul,
    Real.norm_of_nonneg hr.le, mul_inv]
  ring

/-- Angular factor of the kernel on the unit sphere. -/
theorem anisotropicKernel_of_norm_one (ℓ v : Mom d) (hv : ‖v‖ = 1) :
    anisotropicKernel ℓ v = angularSineInv ℓ v := by
  rw [anisotropicKernel, hv, inv_one, one_mul]
  rfl

end WaveTurbulence.WKEL2
