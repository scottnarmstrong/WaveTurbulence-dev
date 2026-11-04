/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsRdown

/-!
# WTParams.R

Wave B tier B1 (WaveB1-Core.lean), source: T (parameters2). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `R_p` for `0 ≤ p ≤ 𝔇` (T (parameters2)). Junk range (stage-1 O2): `R p = R_𝔇` for `p > 𝔇`
(truncated subtraction); statements quantify `p ≤ 𝔇` and use `q = p + 1 ≤ 𝔇`. -/
noncomputable def R (p : ℕ) : ℕ := P.Rdown (P.D - p)

end WTParams
end WaveTurbulence
