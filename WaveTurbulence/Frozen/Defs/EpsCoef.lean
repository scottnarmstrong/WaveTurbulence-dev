/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden

/-!
# epsCoef

Wave B tier B1 (WaveB1-Core.lean), source: T (defcoef0), L556–L561. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- `ε_{k₁k₂k₃}` (T (defcoef0), L556–L561) on lattice indices `kᵢ = nᵢ/L`: `+1` if `k₂ ∉ {k₁, k₃}`,
`-1` if `k₁ = k₂ = k₃`, `0` otherwise. Self-contained (freeze-set closure policy, fix list 3 item 3);
it is the landed `NLS.epsCoef` (bridge `epsCoef_eq_nls`, `WaveB1-Bridges.lean`). -/
def epsCoef {d : ℕ} (n₁ n₂ n₃ : Fin d → ℤ) : ℝ :=
  if n₂ ≠ n₁ ∧ n₂ ≠ n₃ then 1 else if n₁ = n₂ ∧ n₂ = n₃ then -1 else 0

end Decorations
end WaveTurbulence
