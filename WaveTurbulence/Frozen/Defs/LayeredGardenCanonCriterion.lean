/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIncomparable
public import WaveTurbulence.Frozen.Defs.GNodeLeavesBelow
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenCompletelyPaired
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGLeaf
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer

/-!
# LayeredGarden.CanonCriterion

Wave B tier B1 (WaveB1-Core.lean), source: T Prop `canonequiv`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **Canonicity criterion at depth `p + 1`** (T Prop `canonequiv` (i)–(ii), L889): (i) every node
is in layer `≤ p`; (ii) for any two incomparable nodes `𝔫, 𝔫'` (FINDINGS F35) whose subtrees have
completely paired leaves, `max(𝔏_𝔫, 𝔏_{𝔫'}) ≥ min(𝔏_{𝔫^pr}, 𝔏_{𝔫'^pr})`, a root's parent layer
being read as `p`. -/
def CanonCriterion (p : ℕ) : Prop :=
  (∀ a, LG.layer a ≤ p) ∧
    ∀ a a' : GNode LG.garden.tree, a.Incomparable a' →
      LG.garden.CompletelyPaired (a.leavesBelow ∪ a'.leavesBelow) →
        min (LG.parentLayer p a) (LG.parentLayer p a') ≤ max (LG.layer a) (LG.layer a')

end LayeredGarden
end WaveTurbulence
