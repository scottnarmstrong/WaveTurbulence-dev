/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# forestSet

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)

/-- The set of global addresses `(j, p)` (tree index, path) with `p ∈ f (tree j)`. -/
def forestSet (f : TTree → Finset Path) : Finset (Fin w × Path) :=
  Finset.univ.biUnion fun j => (f (tree j)).image (Prod.mk j)

end Forest
end WaveTurbulence
