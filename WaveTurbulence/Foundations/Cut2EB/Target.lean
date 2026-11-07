/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleSum
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.FlowerSumP
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.InstDecidableEqFixPat
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixP

/-! Positive dyadic cut2 targets. The fallback is explicitly requested by CX-C2EB;
it is weaker than the frozen D13 exponent, whose definition is retained too.
Neither target is an assumed analytic input to an assembly theorem. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Cut2EB
open Classical Set

/-- All source binders of the positive-cut2 flower clause, with an explicit gain.
`gain = 1/9` is D13; `gain = 2/25` is the R63 fallback requested in CX-C2EB. -/
def PositiveCut2At (gain : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 : Option ℕ)
        (j₂ : ℕ), 0 < j₂ →
        (∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 (some j₂) ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(gain * Pm)) else 1)

abbrev PositiveCut2FallbackAt := PositiveCut2At (2 / 25)
abbrev PositiveCut2FrozenAt := PositiveCut2At (1 / 9)
abbrev PositiveCut2FallbackInput : Prop := WTPrefixP PositiveCut2FallbackAt
abbrev PositiveCut2FrozenInput : Prop := WTPrefixP PositiveCut2FrozenAt

/-- The fallback exponent in the requested literal notation. -/
theorem fallback_exponent (Pm : ℕ) : -((2 / 25 : ℝ) * Pm) = -(2 * Pm / 25 : ℝ) := by ring

/-- The D13 exponent in the frozen literal notation. -/
theorem frozen_exponent (Pm : ℕ) : -((1 / 9 : ℝ) * Pm) = -(Pm / 9 : ℝ) := by ring

end WaveTurbulence.Cut2EB
