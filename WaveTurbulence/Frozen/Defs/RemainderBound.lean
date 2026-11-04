/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsTheta

/-!
# RemainderBound

Wave B tier B1 (WaveB1-Statements.lean), source: T (ansatz2); L949–L951. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- The remainder hypothesis of `layergarden`: for `q ≤ p`, `R q` is real with
`‖R q‖_{𝔖^{Λ_q,Λ_q}} ≤ L^{-θ_q}` (T (ansatz2), as used at L949–L951). The bound forces `R q ∈ C^{Λ_q}`
(`contDiff_of_SNormR_lt_top`, as `Λ_q = (40d)^{𝔇+1-q} ≥ 1`), which is all TARGET tracks; there is no
smoothness conjunct (`ContDiff ℝ ⊤` is real-analyticity in this Mathlib; stage-3 R1, option B). -/
def RemainderBound (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) : Prop :=
  ∀ q ≤ p, SNormR (P.Lambda q) (P.Lambda q) (R q) ≤ ENNReal.ofReal (P.L ^ (-P.theta q))

end WaveTurbulence
