/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
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

/-! # LG-low (packet L07, item 2): the statement

`LayergardenLowGate` is the low half of the frozen `layergarden` (v1): the body of the sealed `layergarden_v2`
(`Frozen/Theorems/LayergardenV2.lean`, pasted verbatim by `Glue/tools/gen_glue.py`) with `1 / 2 < P.γ →` replaced by
`P.γ ≤ 1 / 2 →` (γ = 1/2 is in this half). With the sealed `layergarden_v2`, `Glue.wtPrefix_of_halves` gives exactly
the frozen `layergarden` (v1) type (`Glue.layergarden_of_low`; checked in `Glue/Exact.lean`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.GammaLow.LGLow

/-- **LG-low**: TARGET Prop `layergarden` (L761–L779; B1.2) for `0 < γ ≤ 1/2`, in the low-half form glued by
`Glue.wtPrefix_of_halves` (the body of the frozen `layergarden_v2`/`layergarden`, verbatim). -/
abbrev LayergardenLowGate : Prop :=
  WTPrefix fun P => P.γ ≤ 1 / 2 →
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
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N))

end WaveTurbulence.GammaLow.LGLow
