/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden

/-!
# Garden.CompletelyPaired

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- A set of leaves is **completely paired** if it contains no marked leaf and the pairing maps it
into itself. -/
def CompletelyPaired (S : Finset (GLeaf G.tree)) : Prop := ∀ ℓ ∈ S, G.pair ℓ ≠ ℓ ∧ G.pair ℓ ∈ S

end Garden
end WaveTurbulence
