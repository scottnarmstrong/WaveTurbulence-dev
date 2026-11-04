/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# WTParams.gamma1

Wave B tier B1 (WaveB1-Core.lean), source: T (defgamma1), L613. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `γ₁ := min(2γ, 1, 2(d-1)(1-γ))` (T (defgamma1), L613). -/
noncomputable def gamma1 : ℝ := min (2 * P.γ) (min 1 (2 * ((P.d : ℝ) - 1) * (1 - P.γ)))

end WTParams
end WaveTurbulence
