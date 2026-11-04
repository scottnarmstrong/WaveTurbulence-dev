/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenCompletelyPaired
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenLeavesBelowSet

/-!
# LayeredGarden.IrreducibleAt

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

/-- The sub-garden rooted at `S` is irreducible: no nonempty proper `A ⊂ S` has completely paired
leaves (T Def `defcanon`: "no proper subset `A` such that the leaves of `𝒯_j^p, j ∈ A`, equal a union
of some `B_i`"). -/
def IrreducibleAt (S : Finset (GNode LG.garden.tree)) : Prop :=
  ∀ A ∈ S.powerset, A.Nonempty → A ≠ S → ¬ LG.garden.CompletelyPaired (LG.leavesBelowSet A)

end LayeredGarden
end WaveTurbulence
