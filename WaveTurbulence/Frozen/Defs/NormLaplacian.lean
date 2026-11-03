/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.PartialDeriv

/-!
# NormLaplacian

Deng–Hani, L285. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The normalized Laplacian `Δ = (2π)⁻¹ (∂²_{x_1} + ⋯ + ∂²_{x_d})` of DH §1.1. -/
def normLaplacian {d : ℕ} (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∑ j, partialDeriv j (partialDeriv j f) x

end WaveTurbulence
