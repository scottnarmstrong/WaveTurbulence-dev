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
public import WaveTurbulence.Foundations.WKE.Existence
public import WaveTurbulence.Foundations.WKE.Uniqueness
public import WaveTurbulence.Foundations.WKEL2.Blowup

/-!
# Provider for `WaveTurbulence.wkelwp`

The proof of the frozen anchor `WaveTurbulence.wkelwp` (Deng–Hani L598–L601, Proposition 3.2,
label `wkelwp`), exported as `WaveTurbulence.Provider.wkelwp`. The maximal time is the Schwartz
lifespan `WKE.tauMax`:

* `0 < τ_max` is `WKE.tauMax_pos`;
* the characterization `τ★ < τ_max ↔ ∃ solution on [0, τ★]` is `WKE.lt_tauMax_iff`;
* uniqueness is `WKE.isWKESolution_unique`;
* the blow-up criterion for every `s > d/2 - 1` is `WKEL2.wkelwp_blowup`, which rests on the
  general-dimension weighted `L²` trilinear estimate (`docs/research/git20-general-d.md`).

The binders `d`, `φin` are implicit and `hd` is an `autoParam`, so that the frozen anchor's body is
exactly `by exact WaveTurbulence.Provider.wkelwp`. This module must not import the frozen anchor.
-/

public section

open Set
open scoped SchwartzMap ENNReal

namespace WaveTurbulence.Provider

/-- **Deng–Hani, Proposition 3.2 (`wkelwp`)**, with the anchor's binders `d`, `φin` implicit and
`hd` an `autoParam`. -/
theorem wkelwp {d : ℕ} (hd : 3 ≤ d := by assumption) {φin : 𝓢(Mom d, ℝ)} :
    ∃ τmax : ℝ≥0∞, 0 < τmax ∧
      (∀ τstar > (0 : ℝ),
        (ENNReal.ofReal τstar < τmax ↔ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ)) ∧
      (∀ τstar > (0 : ℝ), ∀ φ ψ : ℝ → 𝓢(Mom d, ℝ),
        IsWKESolution φin τstar φ → IsWKESolution φin τstar ψ → ∀ τ ∈ Icc 0 τstar, φ τ = ψ τ) ∧
      (τmax < ⊤ → ∀ s : ℝ, (d : ℝ) / 2 - 1 < s → ∀ M : ℝ,
        ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ENNReal.ofReal τ₀ < τmax ∧
          ∀ τstar > τ₀, ENNReal.ofReal τstar < τmax → ∀ φ : ℝ → 𝓢(Mom d, ℝ),
            IsWKESolution φin τstar φ → M < weightedL2Norm s (φ τstar)) :=
  ⟨WKE.tauMax φin, WKE.tauMax_pos (by omega) φin,
    fun _ hτ => WKE.lt_tauMax_iff (by omega) φin hτ,
    fun _ _ _ _ hφ hψ => WKE.isWKESolution_unique (by omega) hφ hψ,
    WKEL2.wkelwp_blowup d hd φin⟩

end WaveTurbulence.Provider
