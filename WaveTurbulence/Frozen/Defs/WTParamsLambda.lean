/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# WTParams.Lambda

Wave B tier B1 (WaveB1-Core.lean), source: T (parameters), L611. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `Λ_p := (40d)^{𝔇-p+1}` (T (parameters), L611), for `0 ≤ p ≤ 𝔇 + 1`; written with exponent
`𝔇 + 1 - p`, which equals `𝔇 - p + 1` in that range (every use has `p ≤ 𝔇 + 1`). Junk range
(stage-1 O2): `Lambda p = 1` for `p > 𝔇 + 1`; no consumer reaches it. -/
def Lambda (p : ℕ) : ℕ := (40 * P.d) ^ (P.D + 1 - p)

end WTParams
end WaveTurbulence
