/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenMatchesCouple
public import WaveTurbulence.Frozen.Defs.RawCpl
public import WaveTurbulence.Frozen.Defs.RawRegular
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# IsRegularCouple

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **A regular couple** (T Def `defreg`). -/
def IsRegularCouple (G : Garden 2) : Prop := ∃ R : RawCpl, RawRegular R ∧ G.MatchesCouple R.1 R.2

end WaveTurbulence
