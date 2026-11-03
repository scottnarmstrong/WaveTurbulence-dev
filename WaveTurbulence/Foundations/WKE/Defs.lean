/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The wave kinetic equation: momentum space, collision operator, solutions

DRAFT definitions of the orchestrator (packet WKE), copied verbatim.

* `Mom d` — momentum space `ℝ^d` (DH (COL), §1.1).
* `collisionOp` — the cubic collision operator `𝒦` of TARGET (COL) (L301–L307), written after the
  change of variables (C.5) (TARGET L2512) with the delta function on the hyperplane `ℓ₁^⊥`.
* `IsWKESolution` — Schwartz-class solutions of (WKE) (TARGET L294–L300).
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace SchwartzMap

namespace WaveTurbulence

/-- Momentum space `ℝ^d` with the Euclidean inner product `⟨k, ℓ⟩ = ∑ kʲ ℓʲ` (DH (COL), §1.1). -/
abbrev Mom (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The cubic collision operator `𝒦(φ₁, φ₂, φ₃)(k)` of (COL), written after the change of
variables `k₁ = k + ℓ₁`, `k₃ = k + ℓ₃`, `k₂ = k + ℓ₁ + ℓ₃` of (C.5) (which removes the first
delta and turns the second into `δ(-2⟨ℓ₁, ℓ₃⟩)`), with `∫ g(ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₃ =
(2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} g`, the integral over the hyperplane `ℓ₁^⊥` taken against its
`(d-1)`-dimensional Lebesgue measure. -/
@[expose] noncomputable def collisionOp {d : ℕ} (φ₁ φ₂ φ₃ : Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ₁ : Mom d, (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ,
    (φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      - φ₁ k * φ₂ (k + ℓ₁ + w) * φ₃ (k + w)
      + φ₁ (k + ℓ₁) * φ₂ k * φ₃ (k + w)
      - φ₁ (k + ℓ₁) * φ₂ (k + ℓ₁ + w) * φ₃ k)

/-- `φ` is a Schwartz-class solution of (WKE) on `[0, τ★]` with initial data `φin`:
`τ ↦ φ τ` is continuous on `[0, τ★]` into the Schwartz space, `φ 0 = φin`, and
`∂_τ φ(τ, k) = 𝒦(φ(τ), φ(τ), φ(τ))(k)` for every `τ ∈ [0, τ★]` and `k ∈ ℝ^d`
(one-sided at the endpoints). -/
@[expose] def IsWKESolution {d : ℕ} (φin : 𝓢(Mom d, ℝ)) (τstar : ℝ) (φ : ℝ → 𝓢(Mom d, ℝ)) :
    Prop :=
  ContinuousOn φ (Icc 0 τstar) ∧ φ 0 = φin ∧
    ∀ τ ∈ Icc 0 τstar, ∀ k : Mom d,
      HasDerivWithinAt (fun s => φ s k) (collisionOp (φ τ) (φ τ) (φ τ) k) (Icc 0 τstar) τ

end WaveTurbulence
