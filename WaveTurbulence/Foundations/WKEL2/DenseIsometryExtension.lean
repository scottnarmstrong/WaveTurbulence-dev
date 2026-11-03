/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.DenseLinearExtension

/-!
# Extending a linear isometry from a dense normed core
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The canonical linear extension of an isometry still preserves every norm. -/
theorem norm_denseExtension_isometry (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (f : V →ₗᵢ[ℝ] F) (u : E) :
    ‖denseExtensionCLM e hd f.toContinuousLinearMap u‖ = ‖u‖ := by
  refine hd.induction ?_ (isClosed_eq (denseExtensionCLM e hd f.toContinuousLinearMap).continuous.norm
    continuous_norm) u
  rintro _ ⟨v, rfl⟩
  rw [denseExtensionCLM_apply, LinearIsometry.coe_toContinuousLinearMap, f.norm_map, e.norm_map]

/-- Isometric extension into a complete codomain. -/
@[expose] def denseIsometryExtension (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (f : V →ₗᵢ[ℝ] F) : E →ₗᵢ[ℝ] F where
  toLinearMap := (denseExtensionCLM e hd f.toContinuousLinearMap).toLinearMap
  norm_map' := norm_denseExtension_isometry e hd f

/-- Agreement at every core point. -/
theorem denseIsometryExtension_apply (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (f : V →ₗᵢ[ℝ] F) (v : V) : denseIsometryExtension e hd f (e v) = f v := by
  change denseExtensionCLM e hd f.toContinuousLinearMap (e v) = _
  rw [denseExtensionCLM_apply, LinearIsometry.coe_toContinuousLinearMap]

end WaveTurbulence.WKEL2
