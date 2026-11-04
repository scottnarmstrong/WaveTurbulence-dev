/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import WaveTurbulence.Frozen.Defs.WeightedL2Norm
public import WaveTurbulence.Provider.Wkelwp

/-!
# Wkelwp

Deng–Hani, L598-L601 (Proposition 3.2, label wkelwp). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **Deng–Hani, Proposition 3.2 (`wkelwp`)** (L598–L601): for Schwartz initial data there is a
maximal time `τ_max ∈ (0, ∞]` such that (WKE) has a Schwartz-class solution on `[0, τ★]`
exactly when `τ★ < τ_max`; the solution is unique; and if `τ_max < ∞` then
`‖⟨k⟩^s φ(τ)‖_{L²} → ∞` as `τ → τ_max` for every `s > d/2 - 1`. -/
theorem wkelwp (d : ℕ) (hd : 3 ≤ d) (φin : 𝓢(Mom d, ℝ)) :
    ∃ τmax : ℝ≥0∞, 0 < τmax ∧
      (∀ τstar > (0 : ℝ),
        (ENNReal.ofReal τstar < τmax ↔ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ)) ∧
      (∀ τstar > (0 : ℝ), ∀ φ ψ : ℝ → 𝓢(Mom d, ℝ),
        IsWKESolution φin τstar φ → IsWKESolution φin τstar ψ → ∀ τ ∈ Icc 0 τstar, φ τ = ψ τ) ∧
      (τmax < ⊤ → ∀ s : ℝ, (d : ℝ) / 2 - 1 < s → ∀ M : ℝ,
        ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ENNReal.ofReal τ₀ < τmax ∧
          ∀ τstar > τ₀, ENNReal.ofReal τstar < τmax → ∀ φ : ℝ → 𝓢(Mom d, ℝ),
            IsWKESolution φin τstar φ → M < weightedL2Norm s (φ τstar)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.wkelwp
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
