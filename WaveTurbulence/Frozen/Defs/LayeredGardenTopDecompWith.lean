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
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopRegion

/-!
# LayeredGarden.TopDecompWith

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

/-- **The decomposition of T Def `defcanon` at one level with given data `(U, Bp)`**, relative to root
nodes `S` and depth `p + 1`, with a predicate `sub` for "the sub-garden rooted at a block is in
`𝒢_p`": attachment nodes `U` in the top region, a partition of `U` into blocks of size `≥ 4` satisfying `sub`, every other node
of the top region in layer `p`, and every leaf of the top region outside `U` either paired with a
leaf of the top region outside `U` (`B_i` of size 2) or, if `flowers`, a flower (`ℋ`). -/
def TopDecompWith (flowers : Bool) (p : ℕ) (sub : Finset (GNode LG.garden.tree) → Prop)
    (S U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U) : Prop :=
  (∀ u ∈ U, LG.TopRegion S U u) ∧
  (∀ a, LG.TopRegion S U a → a ∉ U → LG.layer a = p) ∧
  (∀ ℓ : GLeaf LG.garden.tree, LG.TopRegion S U ℓ.toNode → ℓ.toNode ∉ U →
    (LG.garden.pair ℓ ≠ ℓ ∧ LG.TopRegion S U (LG.garden.pair ℓ).toNode ∧
      (LG.garden.pair ℓ).toNode ∉ U) ∨ (flowers = true ∧ LG.garden.IsFlower ℓ)) ∧
  ∀ B ∈ Bp.parts, 4 ≤ B.card ∧ sub B

end LayeredGarden
end WaveTurbulence
