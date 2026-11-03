/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetWordComponents

/-!
# The genuine coordinate derivative and moment commutator
-/

public section

noncomputable section

open scoped SchwartzMap LineDeriv

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Coordinate differentiation through one coordinate multiplier, including the lower-order term. -/
theorem jetLetterCLM_deriv_moment (i j : Fin d) (f : 𝓢(Mom d, ℝ)) :
    jetLetterCLM (.inr i) (jetLetterCLM (.inl j) f) =
      jetLetterCLM (.inl j) (jetLetterCLM (.inr i) f) +
        (if i = j then (1 : ℝ) else 0) • f := by
  ext k
  simp only [jetLetterCLM, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, coe_coordinateWeightCLM,
    coordinateWeightCLM_apply, add_apply, smul_apply, smul_eq_mul]
  have H := congrArg (fun L : Mom d →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
    (fderiv_fun_mul (EuclideanSpace.proj j).differentiableAt f.differentiableAt (x := k))
  simp only [add_apply, smul_apply, (EuclideanSpace.proj j : Mom d →L[ℝ] ℝ).fderiv] at H
  simpa [EuclideanSpace.proj, EuclideanSpace.single, mul_comm, eq_comm] using H

end WaveTurbulence.WKEL2
