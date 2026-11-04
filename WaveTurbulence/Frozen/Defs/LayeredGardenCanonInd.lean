/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIncomparable
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenCompletelyPaired
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIrreducibleAt
public import WaveTurbulence.Frozen.Defs.LayeredGardenLeavesBelowSet
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecomp

/-!
# LayeredGarden.CanonInd

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

/-- **The inductive class of T Def `defcanon`, read as a decomposition** (B1.11):
`CanonInd p S` means that the layered sub-garden rooted at the (incomparable) nodes `S` belongs to
`𝒢_p` as defined inductively in Def `defcanon`: `𝒢₀ = ∅`; at depth `p+1`, `|S| ≥ 4`, the leaves below
`S` are completely paired, the sub-garden is irreducible, and it decomposes as in `TopDecomp` with
blocks in `𝒢_p`. -/
def CanonInd : ℕ → Finset (GNode LG.garden.tree) → Prop
  | 0, _ => False
  | p + 1, S => 4 ≤ S.card ∧ (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → s.Incomparable s') ∧
      LG.garden.CompletelyPaired (LG.leavesBelowSet S) ∧ LG.IrreducibleAt S ∧
      LG.TopDecomp false p (CanonInd p) S

end LayeredGarden
end WaveTurbulence
