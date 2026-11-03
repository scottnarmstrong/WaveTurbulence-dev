/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# Recovering a derivative from its two product components

Once joint differentiability is established, derivatives of the two
coordinate slices determine the full derivative by linearity.
-/

public section

namespace WaveTurbulence.Fourier

variable {E P H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A jointly differentiable function has the coproduct of its two slice derivatives. -/
theorem hasFDerivAt_of_product_slices {f : E × P → H} {x : E} {y : P}
    {A : E →L[ℝ] H} {B : P →L[ℝ] H} (hd : DifferentiableAt ℝ f (x, y))
    (hA : HasFDerivAt (fun u => f (u, y)) A x)
    (hB : HasFDerivAt (fun v => f (x, v)) B y) :
    HasFDerivAt f (A.coprod B) (x, y) := by
  have heA := (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)).unique hA
  have heB := (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).unique hB
  have he : fderiv ℝ f (x, y) = A.coprod B := by
    apply ContinuousLinearMap.ext
    intro v
    have ha := congrArg (fun T : E →L[ℝ] H => T v.1) heA
    have hb := congrArg (fun T : P →L[ℝ] H => T v.2) heB
    change fderiv ℝ f (x, y) (v.1, 0) = A v.1 at ha
    change fderiv ℝ f (x, y) (0, v.2) = B v.2 at hb
    calc
      _ = fderiv ℝ f (x, y) ((v.1, 0) + (0, v.2)) := by simp
      _ = _ := by rw [map_add, ha, hb]; rfl
  rw [← he]
  exact hd.hasFDerivAt

end WaveTurbulence.Fourier
