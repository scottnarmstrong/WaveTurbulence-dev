/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.leavesOf

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- The leaves of the trees `𝒯_j, j ∈ A`. -/
def leavesOf (A : Finset (Fin w)) : Finset (GLeaf G.tree) :=
  Finset.univ.filter fun ℓ => ℓ.1.1 ∈ A

end Garden
end WaveTurbulence
