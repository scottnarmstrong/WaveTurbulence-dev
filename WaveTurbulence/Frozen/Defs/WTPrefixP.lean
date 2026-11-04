/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# WTPrefixP

Wave B tier B1 (WaveB1-Flower.lean), source: T L2279–L2280. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The prefix `(Π_P)` of `flowerest1` (T L2279–L2280). It is `(Π)` with the moment order `P` chosen after `ν`
("large depending on `C₁`") and before `δ` ("`δ` small depending on `P`"). -/
def WTPrefixP (Q : ℕ → WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ P₀ : ℕ, ∀ Pm : ℕ, P₀ ≤ Pm →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  Q Pm ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

end WaveTurbulence
