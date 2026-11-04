/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenMatchesTreeCouple
public import WaveTurbulence.Frozen.Defs.IsPairedTree
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawRegular
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# IsRegularTree

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **A regular tree** (T Def `defreg`): a paired tree `𝒯` such that `(𝒯, •)` (sign `+`; `(•, 𝒯)` for
sign `-`) is a regular couple with the lone leaf paired with `•`. -/
def IsRegularTree (G : Garden 1) : Prop :=
  IsPairedTree G ∧ ∃ R : RawCpl, RawRegular R ∧ G.MatchesTreeCouple R

end WaveTurbulence
