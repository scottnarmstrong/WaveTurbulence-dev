/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# CollisionOp

Deng–Hani, L299-L307 (COL), L2503 (C.5). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The cubic collision operator `𝒦(φ₁, φ₂, φ₃)(k)` of (COL), written after the change of
variables `k₁ = k + ℓ₁`, `k₃ = k + ℓ₃`, `k₂ = k + ℓ₁ + ℓ₃` of (C.5) (which removes the first
delta and turns the second into `δ(-2⟨ℓ₁, ℓ₃⟩)`), with `∫ g(ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₃ =
(2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} g`, the integral over the hyperplane `ℓ₁^⊥` taken against its
`(d-1)`-dimensional Lebesgue measure. -/
def collisionOp {d : ℕ} (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ₁ : Mom d, (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ,
    (φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      - φ₁ k * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + w)
      - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ k)

end WaveTurbulence
