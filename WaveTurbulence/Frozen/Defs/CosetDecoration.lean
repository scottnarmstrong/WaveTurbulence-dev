/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# cosetDecoration

Wave B tier B1 (WaveB1-Core.lean), source: T L643. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- The vectors of a coset decoration `k_𝔫 = k₀ + z_𝔫 / L` (T L643: for couples and paired trees
with root vector `k₀ ∈ ℝ^d`, `k_𝔫 - k₀ ∈ ℤ_L^d`; `k₀ = 0` gives lattice decorations). As `z` ranges
over the integer decorations with root values `0`, this ranges bijectively over the
`k₀`-decorations (`L ≠ 0`). -/
noncomputable def cosetDecoration {d : ℕ} (L : ℝ) (k : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    GNode G.tree → Mom d :=
  fun a => k + latticePoint L (z a)

end Decorations
end WaveTurbulence
