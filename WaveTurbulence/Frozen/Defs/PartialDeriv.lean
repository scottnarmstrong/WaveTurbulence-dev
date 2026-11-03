/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# PartialDeriv

Deng–Hani, L285. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The partial derivative `∂_{x_j} f(x)`. -/
def partialDeriv {d : ℕ} (j : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  deriv (fun r : ℝ => f (Function.update x j r)) (x j)

end WaveTurbulence
