/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenBelowSet
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableBelowSet

/-!
# LayeredGarden.leavesBelowSet

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The leaves below the nodes of `S`. -/
def leavesBelowSet (S : Finset (GNode LG.garden.tree)) : Finset (GLeaf LG.garden.tree) :=
  Finset.univ.filter fun ℓ => LG.BelowSet S ℓ.toNode

end LayeredGarden
end WaveTurbulence
