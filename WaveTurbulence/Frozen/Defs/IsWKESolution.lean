/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.CollisionOp

/-!
# IsWKESolution

Deng–Hani, L299-L301 (WKE), L598-L601. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- `φ` is a Schwartz-class solution of (WKE) on `[0, τ★]` with initial data `φin`:
`τ ↦ φ τ` is continuous on `[0, τ★]` into the Schwartz space, `φ 0 = φin`, and
`∂_τ φ(τ, k) = 𝒦(φ(τ), φ(τ), φ(τ))(k)` for every `τ ∈ [0, τ★]` and `k ∈ ℝ^d`
(one-sided at the endpoints). -/
def IsWKESolution {d : ℕ} (φin : 𝓢(Mom d, ℝ)) (τstar : ℝ) (φ : ℝ → 𝓢(Mom d, ℝ)) : Prop :=
  ContinuousOn φ (Icc 0 τstar) ∧ φ 0 = φin ∧
    ∀ τ ∈ Icc 0 τstar, ∀ k : Mom d,
      HasDerivWithinAt (fun s => φ s k) (collisionOp (φ τ) (φ τ) (φ τ) k) (Icc 0 τstar) τ

end WaveTurbulence
