/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsTheta

/-!
# InputRemainder

Wave B tier B2 (WaveB2-Statements.lean), source: T L1033. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The input-remainder hypothesis of B2.1/B2.2: `R` real with `‖R‖_{𝔖^{40d,40d}} ≤ L^{-θ_r}` (T L1033,
(ansatz2) with `Λ_p` replaced by `40d`). -/
def InputRemainder (P : WTParams) (R : Mom P.d → ℝ) (r : ℕ) : Prop :=
  SNormR (40 * P.d) (40 * P.d) R ≤ ENNReal.ofReal (P.L ^ (-P.theta r))

end WaveTurbulence
