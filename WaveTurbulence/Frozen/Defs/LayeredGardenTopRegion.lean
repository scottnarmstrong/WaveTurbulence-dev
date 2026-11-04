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
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenBelowSet

/-!
# LayeredGarden.TopRegion

Wave B tier B1 (WaveB1-Statements.lean), source: T Def `defcanon`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The top region of the subtrees rooted at `S` with attachment nodes `U`: the nodes below `S`
having no strict ancestor in `U` (T Def `defcanon`: the trees `𝒯_j^p` with the leaves `U`). -/
def TopRegion (S U : Finset (GNode LG.garden.tree)) (a : GNode LG.garden.tree) : Prop :=
  LG.BelowSet S a ∧ ∀ u ∈ U, u.IsDesc a → u = a

end LayeredGarden
end WaveTurbulence
