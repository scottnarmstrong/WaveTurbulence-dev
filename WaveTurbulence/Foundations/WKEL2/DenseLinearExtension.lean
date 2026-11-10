/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The linear operator extending maps along a dense isometry

This packages the canonical extension as a bounded linear operator on
operator spaces, so each slot of the collision trilinear map can be
extended while preserving the proved norm bound.
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem extend_isometry_apply (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e)
    (f : V →L[ℝ] F) (v : V) : f.extend e.toContinuousLinearMap (e v) = f v := by
  simpa only [LinearIsometry.coe_toContinuousLinearMap] using
    ContinuousLinearMap.extend_eq (e := e.toContinuousLinearMap) f
      hdense e.isometry.isUniformInducing v

/-- Extension along a dense linear isometry is linear in the operator being extended. -/
@[expose] def denseExtensionLM (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e) :
    (V →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] F) where
  toFun f := f.extend e.toContinuousLinearMap
  map_add' f g := by
    apply DFunLike.coe_injective
    apply hdense.equalizer ((f + g).extend e.toContinuousLinearMap).continuous
      (f.extend e.toContinuousLinearMap + g.extend e.toContinuousLinearMap).continuous
    funext v
    change (f + g).extend e.toContinuousLinearMap (e v) =
      (f.extend e.toContinuousLinearMap + g.extend e.toContinuousLinearMap) (e v)
    simp only [add_apply, extend_isometry_apply e hdense]
  map_smul' c f := by
    apply DFunLike.coe_injective
    apply hdense.equalizer ((c • f).extend e.toContinuousLinearMap).continuous
      (c • f.extend e.toContinuousLinearMap).continuous
    funext v
    change (c • f).extend e.toContinuousLinearMap (e v) =
      (c • f.extend e.toContinuousLinearMap) (e v)
    simp only [smul_apply, extend_isometry_apply e hdense]

/-- Extension along a dense isometry does not increase the operator norm. -/
theorem norm_denseExtensionLM_le (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e) (f : V →L[ℝ] F) :
    ‖denseExtensionLM e hdense f‖ ≤ ‖f‖ := by
  have h := ContinuousLinearMap.opNorm_extend_le (e := e.toContinuousLinearMap) (N := 1) f hdense
    (fun v => by simpa only [NNReal.coe_one, one_mul, LinearIsometry.coe_toContinuousLinearMap, e.norm_map] using le_refl ‖v‖)
  simpa only [NNReal.coe_one, one_mul, denseExtensionLM, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- The canonical norm-nonincreasing linear operator on continuous linear maps. -/
@[expose] def denseExtensionCLM (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e) :
    (V →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (denseExtensionLM e hdense).mkContinuous 1 (fun f => by
    simpa only [one_mul] using norm_denseExtensionLM_le e hdense f)

/-- Applying the extension operator does not increase a map's norm. -/
theorem norm_denseExtensionCLM_apply_le (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e)
    (f : V →L[ℝ] F) : ‖denseExtensionCLM e hdense f‖ ≤ ‖f‖ := by
  change ‖denseExtensionLM e hdense f‖ ≤ ‖f‖
  exact norm_denseExtensionLM_le e hdense f

/-- The extension agrees with the original operator at every point of the dense isometric image. -/
theorem denseExtensionCLM_apply (e : V →ₗᵢ[ℝ] E) (hdense : DenseRange e)
    (f : V →L[ℝ] F) (v : V) : denseExtensionCLM e hdense f (e v) = f v :=
  extend_isometry_apply e hdense f v

end WaveTurbulence.WKEL2
