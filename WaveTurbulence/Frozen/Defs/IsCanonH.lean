/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenOnStem

/-!
# IsCanonH

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defflower`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- **Canonical layered flower gardens `ℋ_q`** (T Def `defflower`, last paragraph; criterion form:
"Proposition `canonequiv` also holds for `ℋ_{p+1}`"): a flower garden with all stem nodes in layer
`p`, satisfying `CanonCriterion p` (no irreducibility, no properness). -/
def IsCanonH {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => LG.garden.IsFlowerGarden ∧ (∀ a, LG.OnStem a → LG.layer a = p) ∧
      LG.CanonCriterion p

end WaveTurbulence
