/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsR

/-!
# WTParams.N

Wave B tier B1 (WaveB1-Core.lean), source: T (parameters2). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `N_p = R_p^{40d}` for `0 ≤ p ≤ 𝔇` (T (parameters2)). -/
noncomputable def N (p : ℕ) : ℕ := P.R p ^ (40 * P.d)

end WTParams
end WaveTurbulence
