/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.IsDecoration

/-!
# IntDecoration

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defdec`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- The **integer `(n₁,…,n_w)`-decorations** (T Def `defdec`): decorations by lattice indices
`κ_𝔫 ∈ ℤ^d` (the vector of node `𝔫` is `κ_𝔫 / L`, `latticePoint L κ_𝔫`) with root values
`κ_{𝔯_j} = n_j`. -/
def IntDecoration (d : ℕ) (n : Fin w → (Fin d → ℤ)) : Type :=
  {κ : GNode G.tree → (Fin d → ℤ) // IsDecoration G κ ∧ ∀ j, κ (GNode.root G.tree j) = n j}

end Decorations
end WaveTurbulence
