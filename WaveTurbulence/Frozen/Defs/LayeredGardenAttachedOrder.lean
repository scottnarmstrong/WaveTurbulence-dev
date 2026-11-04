/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeOrderBelow
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachLinkedOn
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes

/-!
# LayeredGarden.attachedOrder

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgtr`, L731–L732. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The order of the attached garden containing `u`: the total order of the subtrees rooted at the
attachment nodes `AttachLinkedOn`-equivalent to `u`. -/
noncomputable def attachedOrder (p : ℕ) (u : GNode LG.garden.tree) : ℕ := by
  classical
  exact ∑ u' ∈ (LG.attachNodes p).filter (fun u' => Relation.EqvGen (LG.AttachLinkedOn p) u u'),
    u'.orderBelow

end LayeredGarden
end WaveTurbulence
