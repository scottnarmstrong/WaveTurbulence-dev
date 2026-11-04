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
# WTPrefix

Wave B tier B1 (WaveB1-Core.lean), source: WAVE-B §1.2; T L605–L615. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- **The parameter prefix (Π)** (WAVE-B §1.2; T L605–L615 and FINDINGS F5): `P` holds for all
parameters chosen in TARGET's order `d, γ → η → φin, τ★, φ → C₁ → ν → δ, 𝔇 → C₂ → L`, each
"small" or "large" choice being eventual (`∃` threshold, `∀` beyond it) and each constant `Cⱼ`
existential right after the quantities it may depend on. -/
def WTPrefix (P : WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  P ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

end WaveTurbulence
