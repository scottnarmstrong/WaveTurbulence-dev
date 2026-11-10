/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.DenseLinearExtension
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Extending a bounded trilinear map from a dense isometric core
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

-- Cache the intermediate operator spaces before synthesizing the third level.
local instance normedVF : NormedAddCommGroup (V →L[ℝ] F) := inferInstance
local instance spaceVF : NormedSpace ℝ (V →L[ℝ] F) := inferInstance
local instance normedVVF : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] F) := inferInstance
local instance spaceVVF : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] F) := inferInstance
local instance normedEF : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance spaceEF : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance normedEEF : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance spaceEEF : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Extend the last slot of a curried trilinear map. -/
@[expose] def extendTrilinearLast (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (T : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) : V →L[ℝ] V →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ V (V →L[ℝ] F) (E →L[ℝ] F)
    (denseExtensionCLM e hd)).comp T

/-- Extend all three slots, keeping the actual original values on the dense core. -/
@[expose] def denseTrilinearExtension (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (T : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) : E →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
  denseExtensionCLM e hd
    ((denseExtensionCLM e hd).comp (extendTrilinearLast e hd T))

/-- Agreement of the continuous extension with its trilinear core. -/
theorem denseTrilinearExtension_apply (e : V →ₗᵢ[ℝ] E) (hd : DenseRange e)
    (T : V →L[ℝ] V →L[ℝ] V →L[ℝ] F) (x y z : V) :
    denseTrilinearExtension e hd T (e x) (e y) (e z) = T x y z := by
  simp only [denseTrilinearExtension, denseExtensionCLM_apply,
    ContinuousLinearMap.comp_apply, extendTrilinearLast,
    ContinuousLinearMap.compL_apply]

end WaveTurbulence.WKEL2
