/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsBalancedSig
public import WaveTurbulence.Frozen.Defs.JbrProd
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.WTPrefix
import WaveTurbulence.Foundations.GammaLow.Glue.Layergarden
import WaveTurbulence.Foundations.GammaLow.Close.Halves

/-!
# Provider for `WaveTurbulence.layergarden`

The proof of the frozen anchor `WaveTurbulence.layergarden` (T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762) is assembled here under the export
`WaveTurbulence.Provider.layergarden`.
The proof is the L07 glue `GammaLow.Glue.layergarden_of_low` (`Foundations/GammaLow/Glue/Layergarden`:
`wtPrefix_of_halves` of the sealed `layergarden_v2` and the low half) applied to the closed LG-low
theorem `WaveTurbulence.GammaLow.Close.layergarden_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Halves`).
The proof modules are imported privately (`import`), so that the frozen anchor
elaborates its statement in its freeze environment. This module must not import its own frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- The frozen statement of `WaveTurbulence.layergarden`, verbatim,
proved by the assembly in the module docstring. -/
theorem layergarden : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N)) :=
  WaveTurbulence.GammaLow.Glue.layergarden_of_low WaveTurbulence.GammaLow.Close.layergarden_low_closed

end WaveTurbulence.Provider
