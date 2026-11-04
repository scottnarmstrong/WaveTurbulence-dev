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
public import WaveTurbulence.Frozen.Defs.GardenInstDecidableCompletelyPaired
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGLeaf
public import WaveTurbulence.Frozen.Defs.InstDecidableIncomparable
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonCriterion
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer

/-!
# LayeredGarden.instDecidableCanonCriterion

Wave B tier B1 (WaveB1-Core.lean), source: — (Decidable instance for `CanonCriterion`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

@[instance_reducible, instance] def instDecidableCanonCriterion (p : ℕ) :
    Decidable (LG.CanonCriterion p) := by
  unfold CanonCriterion
  infer_instance

end LayeredGarden
end WaveTurbulence
