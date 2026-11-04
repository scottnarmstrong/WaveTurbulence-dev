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
# chosenSet

Wave B tier B2 (WaveB2-Regular.lean), source: T Prop `deflink`; DH21 Def 4.11. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **`𝒩^ch`** (T Prop `deflink`, last paragraph; DH21 Def 4.11, review P6): one node of each link. -/
def chosenSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path))) : Finset (Fin w × Path) :=
  (links.map Prod.fst).toFinset

end WaveTurbulence
