/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AnisotropicScaling
public import WaveTurbulence.Foundations.WKEL2.AngularCoordinates

/-!
# Symmetry and measurability of the angular sine kernel
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Squared length of the transverse projection from a unit direction. -/
theorem norm_perpPart_sq_of_unit {u : Mom d} (hu : ‖u‖ = 1) (v : Mom d) :
    ‖(perpPart u v : Mom d)‖ ^ 2 = ‖v‖ ^ 2 - ⟪u, v⟫_ℝ ^ 2 := by
  rw [coe_perpPart, unitVec_of_norm_one hu, norm_sub_sq_real,
    inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu, one_pow, mul_one]
  rw [real_inner_comm v u]
  ring

/-- The sine denominator is symmetric on the unit sphere. -/
theorem angularSineInv_symm {u v : Mom d} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angularSineInv u v = angularSineInv v u := by
  unfold angularSineInv
  congr 1
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_perpPart_sq_of_unit hu, norm_perpPart_sq_of_unit hv, hu, hv, real_inner_comm u v]

/-- Joint measurability of the sine kernel on two unit spheres. -/
theorem measurable_sphereSineInv :
    Measurable (fun p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 =>
      angularSineInv p.1.1 p.2.1) := by
  have hc : Continuous (fun p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1 =>
      (p.2.1 : Mom d) - ⟪(p.1.1 : Mom d), (p.2.1 : Mom d)⟫_ℝ • p.1.1) := by fun_prop
  have heq (p : sphere (0 : Mom d) 1 × sphere (0 : Mom d) 1) :
      angularSineInv p.1.1 p.2.1 =
        ‖(p.2.1 : Mom d) - ⟪(p.1.1 : Mom d), (p.2.1 : Mom d)⟫_ℝ • p.1.1‖⁻¹ := by
    rw [angularSineInv, coe_perpPart,
      unitVec_of_norm_one (mem_sphere_zero_iff_norm.mp p.1.2)]
  simp_rw [heq]
  exact hc.measurable.norm.inv

end WaveTurbulence.WKEL2
