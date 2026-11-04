/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIsDesc
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGNode
public import WaveTurbulence.Frozen.Defs.InstDecidableIsDesc
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenBelowSet
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableBelowSet
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopRegion

/-!
# LayeredGarden.instDecidableTopRegion

Wave B tier B1 (WaveB1-Statements.lean), source: — (Decidable instance for `TopRegion`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

@[instance_reducible, instance] def instDecidableTopRegion (S U : Finset (GNode LG.garden.tree))
    (a : GNode LG.garden.tree) : Decidable (LG.TopRegion S U a) := by
  unfold TopRegion
  infer_instance

end LayeredGarden
end WaveTurbulence
