/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IterPartial
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.MaxBracketPow
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TimeFT

/-!
# XNorm

Wave B tier B1 (WaveB1-System.lean), source: T (normX), L581. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

open Classical in
/-- **`‖F‖_{𝔛^{θ,Λ₁,Λ₂}}`** (T (normX), L581) for `F(t₁,…,t_r, k)`: `max_{|ρ| ≤ Λ₁} ∫ max_i⟨λ_i⟩^θ
‖⟨k⟩^{Λ₂} ∂_k^ρ F̂(λ, k)‖_{L^∞_k} dλ`; `⊤` unless every `t ↦ F(t,k)` is integrable and, for `Λ₁ ≥ 1`,
`k ↦ F̂(λ,k)` is `C^{Λ₁}` for almost every `λ` (F80). This is the guard of TARGET's norm and of the landed
`Fourier.MixedFourierAdmissible`. A per-frequency `⊤` inside the integral would make `∫⁻` a lower integral of a
possibly non-measurable integrand: the norm could be smaller than TARGET's and would have no triangle inequality.
With the a.e. guard the integrand is a.e. equal to a Borel function, so `∫⁻` is a genuine integral. For `Λ₁ = 0`
no momentum regularity is imposed (the source's `L^∞_k` needs none, and `k` often ranges over a lattice:
orchestrator ruling, fix list 3 item 2). Reading (stage-2 O1): the integrability
guard makes the unrestricted norm `⊤` for some functions with finite source norm (e.g. `sinc`);
the restricted norms over bounded `ℬ`, the only use, agree with TARGET's up to an absolute factor
(multiply by a cutoff equal to `1` on `ℬ`; Peetre). -/
noncomputable def XNorm {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  if (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam)) then
    ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁), ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
      ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖)
  else ⊤

end Norms
end WaveTurbulence
