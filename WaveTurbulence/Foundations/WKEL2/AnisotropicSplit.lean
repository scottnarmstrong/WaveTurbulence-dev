/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisFar
public import WaveTurbulence.Foundations.WKEL2.AxisCoordinates

/-!
# Transporting the cylindrical near/far estimates to an arbitrary axis
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The near anisotropic kernel in cylindrical unit-box coordinates. -/
@[expose] def anisotropicNear {ℓ : Mom d} (hℓ : ℓ ≠ 0) (u : Mom d) : ℝ :=
  (ball (0 : ℝ × Mom (d - 1)) 1).indicator (axisKernel 1) ((axisSliceEquiv hℓ).symm u)

/-- The complementary anisotropic far kernel. -/
@[expose] def anisotropicFar {ℓ : Mom d} (hℓ : ℓ ≠ 0) (u : Mom d) : ℝ :=
  (ball (0 : ℝ × Mom (d - 1)) 1)ᶜ.indicator (axisKernel 1) ((axisSliceEquiv hℓ).symm u)

theorem anisotropicNear_nonneg {ℓ : Mom d} (hℓ : ℓ ≠ 0) (u : Mom d) :
    0 ≤ anisotropicNear hℓ u := indicator_nonneg (fun x _ => axisKernel_nonneg 1 x) _

theorem anisotropicFar_nonneg {ℓ : Mom d} (hℓ : ℓ ≠ 0) (u : Mom d) :
    0 ≤ anisotropicFar hℓ u := indicator_nonneg (fun x _ => axisKernel_nonneg 1 x) _

/-- Exact near/far decomposition, with no excluded axis points. -/
theorem anisotropicNear_add_anisotropicFar {ℓ : Mom d} (hℓ : ℓ ≠ 0) (u : Mom d) :
    anisotropicNear hℓ u + anisotropicFar hℓ u = anisotropicKernel ℓ u := by
  have hsum := congrFun (indicator_self_add_compl (ball (0 : ℝ × Mom (d - 1)) 1)
    (axisKernel 1)) ((axisSliceEquiv hℓ).symm u)
  have hid := anisotropicKernel_axisSlice hℓ ((axisSliceEquiv hℓ).symm u)
  rw [(axisSliceEquiv hℓ).apply_symm_apply] at hid
  exact hsum.trans hid.symm

theorem measurable_anisotropicNear {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Measurable (anisotropicNear hℓ) :=
  ((measurable_axisKernel 1).indicator measurableSet_ball).comp (axisSliceEquiv hℓ).symm.measurable

theorem measurable_anisotropicFar {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Measurable (anisotropicFar hℓ) :=
  ((measurable_axisKernel 1).indicator measurableSet_ball.compl).comp (axisSliceEquiv hℓ).symm.measurable

/-- Near integrability is uniform under rotations of the axis. -/
theorem integrable_anisotropicNear (hd : 3 ≤ d) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (anisotropicNear hℓ) := by
  have hsymm := MeasurePreserving.symm (axisSliceEquiv hℓ) (measurePreserving_axisSliceEquiv hℓ)
  exact hsymm.integrable_comp_of_integrable (integrable_axisKernel_near (by omega : 2 ≤ d - 1))

/-- The near mass is independent of the axis. -/
theorem integral_anisotropicNear {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    (∫ u, anisotropicNear hℓ u) =
      ∫ z : ℝ × Mom (d - 1), (ball 0 1).indicator (axisKernel 1) z ∂volume.prod volume := by
  have hsymm := MeasurePreserving.symm (axisSliceEquiv hℓ) (measurePreserving_axisSliceEquiv hℓ)
  exact hsymm.integral_comp' (fun z : ℝ × Mom (d - 1) => (ball 0 1).indicator (axisKernel 1) z)

/-- Far Lᵖ membership in the full M₁ range. -/
theorem memLp_anisotropicFar (hd : 3 ≤ d) {ℓ : Mom d} (hℓ : ℓ ≠ 0)
    (p : ℝ) (hlo : (d : ℝ) < 2 * p) (hhi : p < (d : ℝ) - 1) :
    MemLp (anisotropicFar hℓ) (ENNReal.ofReal p) := by
  have hp := memLp_axisKernel_far (by omega : 2 ≤ d - 1) p
    (by rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num; linarith only [hlo])
    (by rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num; exact hhi)
  exact hp.comp_measurePreserving
    (MeasurePreserving.symm (axisSliceEquiv hℓ) (measurePreserving_axisSliceEquiv hℓ))

/-- The far power integral is independent of the axis. -/
theorem integral_anisotropicFar_norm_rpow {ℓ : Mom d} (hℓ : ℓ ≠ 0) (p : ℝ) :
    (∫ u, ‖anisotropicFar hℓ u‖ ^ p) =
      ∫ z : ℝ × Mom (d - 1), ‖(ball 0 1)ᶜ.indicator (axisKernel 1) z‖ ^ p
        ∂volume.prod volume := by
  have hsymm := MeasurePreserving.symm (axisSliceEquiv hℓ) (measurePreserving_axisSliceEquiv hℓ)
  exact hsymm.integral_comp' (fun z : ℝ × Mom (d - 1) =>
    ‖(ball 0 1)ᶜ.indicator (axisKernel 1) z‖ ^ p)

end WaveTurbulence.WKEL2
