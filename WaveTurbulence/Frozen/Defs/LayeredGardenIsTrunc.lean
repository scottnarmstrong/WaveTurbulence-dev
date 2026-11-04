/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachedOrder
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopOrder

/-!
# LayeredGarden.IsTrunc

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defgtr`, L731–L732; T L2288. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **Truncation** (T Def `defgtr`, L731–L732, without construction data; the flower version
`ℋ^tr`, T L2288, is the same predicate): every top tree has order `≤ Ntop` and every attached garden
has order `≤ Natt`. TARGET uses `Ntop = N_{p+1}`, `Natt = N_p`. -/
def IsTrunc (p Ntop Natt : ℕ) : Prop :=
  (∀ j, LG.topOrder p j ≤ Ntop) ∧ ∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ Natt

end LayeredGarden
end WaveTurbulence
