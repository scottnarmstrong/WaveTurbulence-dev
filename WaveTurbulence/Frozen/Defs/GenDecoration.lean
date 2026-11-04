/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.IsDecoration

/-!
# GenDecoration

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defflower`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- The **general integer decorations** used by the one kernel `kernelK`: root values `n_j` and,
at every flower, the value `n'` (T Def `defflower`: `(k, k')`-decorations). For plain gardens and
paired trees the flower condition is void. -/
def GenDecoration (d : ℕ) (n : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ) : Type :=
  {κ : GNode G.tree → (Fin d → ℤ) // IsDecoration G κ ∧ (∀ j, κ (GNode.root G.tree j) = n j) ∧
    ∀ ℓ : GLeaf G.tree, G.IsFlower ℓ → κ ℓ.toNode = n'}

end Decorations
end WaveTurbulence
