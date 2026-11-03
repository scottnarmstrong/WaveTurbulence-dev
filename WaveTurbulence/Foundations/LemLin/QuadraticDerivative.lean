/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicTranslation
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Coordinate derivatives of the two cubic phases

Exact polynomial identities used in repeated integration by parts for
TARGET `lemcubic0`.
-/

public section

namespace WaveTurbulence.LemLin

/-- The only diagonal quadratic term occurs at `z` in the collision phase. -/
@[expose] def quadraticDiagonal (kind : CubicPhase) (s : ℝ) (j : Fin 3) : ℝ :=
  match kind with
  | .cross => 0
  | .collision => if j = 2 then -s else 0

/-- The exact one-coordinate Taylor polynomial (the phase is quadratic). -/
theorem scalarQuadratic_update (kind : CubicPhase) (s t : ℝ)
    (p : Fin 3 → ℝ) (j : Fin 3) (u : ℝ) :
    scalarQuadratic kind s t (Function.update p j u) =
      scalarQuadratic kind s t p + cubicFrequencyShift kind s t p j * (u - p j) +
        quadraticDiagonal kind s j * (u - p j) ^ 2 := by
  cases kind <;> fin_cases j <;>
    simp [scalarQuadratic, cubicFrequencyShift, quadraticDiagonal, Function.update] <;> ring

/-- The gradient is exactly the frequency shift from polarization. -/
theorem hasDerivAt_scalarQuadratic_update (kind : CubicPhase) (s t : ℝ)
    (p : Fin 3 → ℝ) (j : Fin 3) :
    HasDerivAt (fun u => scalarQuadratic kind s t (Function.update p j u))
      (cubicFrequencyShift kind s t p j) (p j) := by
  have hlin := (hasDerivAt_id (p j)).sub_const (p j)
  have h := ((hlin.const_mul (cubicFrequencyShift kind s t p j)).const_add
    (scalarQuadratic kind s t p)).add
      ((hlin.pow 2).const_mul (quadraticDiagonal kind s j))
  simpa [scalarQuadratic_update, Pi.add_def, Pi.pow_def] using h

end WaveTurbulence.LemLin
