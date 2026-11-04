/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecompWith

/-!
# LayeredGarden.TopDecomp

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

/-- `TopDecompWith` for some construction data `(U, Bp)`. -/
def TopDecomp (flowers : Bool) (p : ℕ) (sub : Finset (GNode LG.garden.tree) → Prop)
    (S : Finset (GNode LG.garden.tree)) : Prop :=
  ∃ U : Finset (GNode LG.garden.tree), ∃ Bp : Finpartition U, LG.TopDecompWith flowers p sub S U Bp

end LayeredGarden
end WaveTurbulence
