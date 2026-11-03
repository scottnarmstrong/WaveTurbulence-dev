/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Frozen.Defs.NormLaplacian
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff

/-!
# IsSmoothNLSSolution

Deng–Hani, L278-L283 (NLS), L292 (DAT), L314-L316. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- `u` is a smooth solution on `[0, T]` of (NLS) `(i∂_t - Δ)u + α|u|²u = 0` on `𝕋_L^d`,
whose initial datum `u(0, ·)` has Fourier coefficients `û(0, n/L) = c n`: `u` is `C^∞` on
`[0, T] × ℝ^d`, `L`-periodic in each space variable, and satisfies the equation pointwise
(one-sided time derivative at `t = 0, T`). -/
def IsSmoothNLSSolution {d : ℕ} (L α T : ℝ) (c : (Fin d → ℤ) → ℂ)
    (u : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2) (Icc 0 T ×ˢ univ) ∧
    (∀ t ∈ Icc 0 T, ∀ x : Fin d → ℝ, ∀ j : Fin d, u t (x + Pi.single j L) = u t x) ∧
    (∀ n : Fin d → ℤ, torusFourierCoeff L (u 0) n = c n) ∧
    ∀ t ∈ Icc 0 T, ∀ x : Fin d → ℝ,
      I * derivWithin (fun s => u s x) (Icc 0 T) t - normLaplacian (u t) x
        + (α : ℂ) * ((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x = 0

end WaveTurbulence
