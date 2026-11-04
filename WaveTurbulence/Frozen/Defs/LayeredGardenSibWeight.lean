/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsFlowerNode
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.sibWeight

Wave B tier B1 (WaveB1-Flower.lean), source: T L2327. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)
variable {d : ℕ}

open Classical in
/-- The `†` weight (T L2327): the children of each `𝔣^pr` other than the flower carry the prescribed
vectors `c j i`. -/
noncomputable def sibWeight (c : Fin w → Fin 3 → Mom d) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ b : GBranch LG.garden.tree, if LG.garden.IsFlowerParent b then
    ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then 1 else
      if k (b.child i) = c b.1.1 i then 1 else 0) else 1

end LayeredGarden
end WaveTurbulence
