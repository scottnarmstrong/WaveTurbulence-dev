/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# WTParams.theta

Wave B tier B1 (WaveB1-Core.lean), source: T (parameters), L611. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

/-- `θ_p := η^{20} (1 + 2^{-p})` (T (parameters), L611). -/
noncomputable def theta (p : ℕ) : ℝ := P.η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ p)

end WTParams
end WaveTurbulence
