/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenCompletelyPaired
public import WaveTurbulence.Frozen.Defs.GardenLeavesOf

/-!
# Garden.Irreducible

Wave B tier B1 (WaveB1-Core.lean), source: T L636. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- **Irreducible** (T L636): there is no `A ⊆ {1,…,w}` with `A ≠ ∅`, `A ≠` everything, such that
the leaves of the trees `𝒯_j, j ∈ A`, are all paired with each other. -/
def Irreducible : Prop :=
  ∀ A : Finset (Fin w), A.Nonempty → A ≠ Finset.univ → ¬ G.CompletelyPaired (G.leavesOf A)

end Garden
end WaveTurbulence
