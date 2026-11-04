/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ChosenSet
public import WaveTurbulence.Frozen.Defs.InstDecidableIsSpecialSet
public import WaveTurbulence.Frozen.Defs.IsSpecialSet
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# specialSets

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The special subsets of `𝒩^ch` (a finite set). -/
def specialSets {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path))) :
    Finset (Finset (Fin w × Path)) :=
  (chosenSet links).powerset.filter (IsSpecialSet links)

end WaveTurbulence
