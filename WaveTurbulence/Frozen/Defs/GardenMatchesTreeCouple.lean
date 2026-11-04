/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableIsLone
public import WaveTurbulence.Frozen.Defs.GardenIsLone
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawCplTree
public import WaveTurbulence.Frozen.Defs.SymmPairs
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.MatchesTreeCouple

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- A paired tree `G` of sign `ζ` seen as the couple `(𝒯, •)` (sign `+`) or `(•, 𝒯)` (sign `-`), with
the lone leaf paired with `•`, has the raw data `R`. -/
def Garden.MatchesTreeCouple (G : Garden 1) (R : RawCpl) : Prop :=
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  R.tree s = G.tree 0 ∧ R.tree (1 - s) = .leaf ∧
    ∀ ℓ : GLeaf G.tree,
      let z : Fin 2 × Path := (s, ℓ.1.2)
      let y : Fin 2 × Path := if G.IsLone ℓ then (1 - s, []) else (s, (G.pair ℓ).1.2)
      (z, y) ∈ symmPairs R.2

end WaveTurbulence
