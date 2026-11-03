/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Bundling a bounded algebraic trilinear map
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance boundedNormedVF : NormedAddCommGroup (V →L[ℝ] F) := inferInstance
local instance boundedSpaceVF : NormedSpace ℝ (V →L[ℝ] F) := inferInstance
local instance boundedNormedVVF : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] F) := inferInstance
local instance boundedSpaceVVF : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] F) := inferInstance

/-- First bundle the two inner slots, retaining algebraic linearity in the outer slot. -/
@[expose] def boundedTrilinearInner (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] F)
    (C : ℝ) (hb : ∀ x y z, ‖A x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) :
    V →ₗ[ℝ] V →L[ℝ] V →L[ℝ] F where
  toFun x := (A x).mkContinuous₂ (C * ‖x‖) (hb x)
  map_add' x y := by
    ext v w
    simp only [LinearMap.mkContinuous₂_apply, map_add, LinearMap.add_apply]
    rfl
  map_smul' c x := by
    ext v w
    simp only [LinearMap.mkContinuous₂_apply, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]
    rfl

/-- A trilinear bound supplies the continuous trilinear map, without extra hypotheses. -/
@[expose] def boundedTrilinear (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y z, ‖A x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) :
    V →L[ℝ] V →L[ℝ] V →L[ℝ] F :=
  (boundedTrilinearInner A C hb).mkContinuous C (fun x =>
    (A x).mkContinuous₂_norm_le (mul_nonneg hC (norm_nonneg x)) (hb x))

/-- Bundling preserves each value of the original map. -/
theorem boundedTrilinear_apply (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y z, ‖A x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) (x y z : V) :
    boundedTrilinear A C hC hb x y z = A x y z := rfl

/-- The trilinear operator norm is at most the proved constant. -/
theorem norm_boundedTrilinear_le (A : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y z, ‖A x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) :
    ‖boundedTrilinear A C hC hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end WaveTurbulence.WKEL2
