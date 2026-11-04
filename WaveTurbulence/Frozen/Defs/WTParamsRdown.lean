/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# WTParams.Rdown

Wave B tier B1 (WaveB1-Core.lean), source: T (parameters2), L612. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `R_{𝔇-k}` by downward recursion (T (parameters2), L612): `R_𝔇 = ⌊(log L)^{40d}⌋` and
`R_{p-1} = N_p^{40d} = (R_p^{40d})^{40d}`. -/
noncomputable def Rdown : ℕ → ℕ
  | 0 => ⌊Real.log P.L ^ (40 * P.d)⌋₊
  | k + 1 => (Rdown k ^ (40 * P.d)) ^ (40 * P.d)

end WTParams
end WaveTurbulence
