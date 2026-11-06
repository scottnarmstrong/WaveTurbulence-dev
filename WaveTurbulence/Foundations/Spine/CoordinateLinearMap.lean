/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeBound
/-! Coordinate reconstruction and the finite-dimensional operator norm estimate used for
uniform limits of the source approximation derivatives. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def coordinateLinearMap {d : ℕ} (v : Fin d → ℂ) : Mom d →L[ℝ] ℂ :=
  ∑ j, (PiLp.proj 2 (fun _ : Fin d => ℝ) j).smulRight (v j)

theorem coordinateLinearMap_apply {d : ℕ} (v : Fin d → ℂ) (x : Mom d) :
    coordinateLinearMap v x = ∑ j, (x j) • v j := by
  simp only [coordinateLinearMap, _root_.sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]

theorem coordinateLinearMap_single {d : ℕ} (v : Fin d → ℂ) (i : Fin d) :
    coordinateLinearMap v (EuclideanSpace.single i 1) = v i := by
  rw [coordinateLinearMap_apply]
  simp

theorem norm_clm_le_sum_coordinates {d : ℕ} (T : Mom d →L[ℝ] ℂ) :
    ‖T‖ ≤ ∑ j, ‖T (EuclideanSpace.single j 1)‖ := by
  refine T.opNorm_le_bound (sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  have he : x = ∑ j : Fin d, (x j) • EuclideanSpace.single j (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp
  have hexpand : T x = ∑ j : Fin d, (x j) • T (EuclideanSpace.single j 1) := by
    conv_lhs => rw [he]
    simp only [map_sum, map_smul]
  rw [hexpand]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, ‖x‖ * ‖T (EuclideanSpace.single j 1)‖ := by
      apply sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
        (norm_nonneg _)
    _ = _ := by rw [← mul_sum, mul_comm]

theorem norm_fderiv_sub_coordinateLinearMap_le {d : ℕ} (f : Mom d → ℂ)
    (v : Fin d → ℂ) (x : Mom d) :
    ‖fderiv ℝ f x - coordinateLinearMap v‖ ≤ ∑ j, ‖partialMom j f x - v j‖ := by
  have h := norm_clm_le_sum_coordinates (fderiv ℝ f x - coordinateLinearMap v)
  simpa only [ContinuousLinearMap.sub_apply, coordinateLinearMap_single, partialMom] using h

end WaveTurbulence.LGSpine
