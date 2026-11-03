/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# TorusFourierCoeff

Deng–Hani, L286-L288 (fourier). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The space Fourier coefficient (DH (1.2)):
`f̂(k) = L^{-d/2} ∫_{[0,L]^d} f(x) e^{-2πi k·x} dx` at `k = n / L ∈ ℤ_L^d`. -/
def torusFourierCoeff {d : ℕ} (L : ℝ) (f : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L),
      f x * exp (-(2 * Real.pi * ∑ j, (n j : ℝ) / L * x j : ℝ) * I)

end WaveTurbulence
