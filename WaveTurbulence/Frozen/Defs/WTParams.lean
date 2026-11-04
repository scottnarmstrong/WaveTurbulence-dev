/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# WTParams

Wave B tier B1 (WaveB1-Core.lean), source: L605–L615. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- The parameters fixed in T §2.4.2 (L605–L615), in the order in which TARGET chooses them:
`d, γ` (and the absolute constant `C₀(d,γ)`), `η`, the data `φin, τ★, φ`, `C₁`, `ν`, `δ`
(with `𝔇 = τ★/δ ∈ ℤ`), `C₂`, `L`. The constraints between them are imposed by `WTPrefix`. -/
structure WTParams where
  /-- dimension -/
  d : ℕ
  /-- the exponent `γ ∈ (0,1)` of `α = L^{-γ}` -/
  γ : ℝ
  /-- the small parameter `η` (depends only on `C₀(d,γ)`) -/
  η : ℝ
  /-- the initial data of (WKE) -/
  φin : SchwartzMap (Mom d) ℝ
  /-- the final kinetic time `τ★` -/
  τstar : ℝ
  /-- the solution of (WKE) on `[0, τ★]` -/
  φ : ℝ → SchwartzMap (Mom d) ℝ
  /-- the constant `C₁ = C₁(d,γ,η,τ★,𝔆)` -/
  C₁ : ℝ
  /-- the small parameter `ν` (depends on `C₁`) -/
  ν : ℝ
  /-- the step `δ` (depends on `ν`), with `τ★ = 𝔇 δ` -/
  δ : ℝ
  /-- the number of steps `𝔇 = τ★ / δ ∈ ℤ` -/
  D : ℕ
  /-- the constant `C₂ = C₂(𝔇, δ, φin)` -/
  C₂ : ℝ
  /-- the size `L` of the torus (large depending on `C₂`) -/
  L : ℝ

end WaveTurbulence
