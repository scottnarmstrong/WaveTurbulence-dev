/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Joint coordinate and its exact resonance, including vine (I)

Fixing two external momenta with gap r, a joint is parametrized by the
difference of its incoming internal label and an external label. This is
an integral affine bijection, including m=0 and zero gap.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- The single joint coordinate x₀=e−c. -/
@[expose] def jointChart {E : Type*} [AddCommGroup E] (e : E) : E ≃ E where
  toFun := fun c => e-c
  invFun := fun x => e-x
  left_inv := by intro c; exact sub_sub_cancel e c
  right_inv := by intro x; exact sub_sub_cancel e x

/-- TARGET Omegax_0: two pairs with the same gap give a linear joint phase. -/
theorem joint_resonance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e c r : E) :
    ‖e‖^2-‖e-r‖^2-‖c‖^2+‖c-r‖^2=2*inner ℝ r (jointChart e c) := by
  change ‖e‖^2-‖e-r‖^2-‖c‖^2+‖c-r‖^2=2*inner ℝ r (e-c)
  simp only [norm_sub_sq_real,inner_sub_right,real_inner_comm]
  ring

end WaveTurbulence.Vine.Param
