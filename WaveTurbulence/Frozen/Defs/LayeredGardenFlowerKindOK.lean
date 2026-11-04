/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsFlowerNode
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopCountBelow
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopOrder
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.FlowerKindOK

Wave B tier B1 (WaveB1-Flower.lean), source: T L2290. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **The kind restrictions on the initial flower trees.** "Order" means the number of layer-`p` branching
nodes (T L2290).
- `X`: `1 ≤` order `≤ N_{p+1}`. The `1 ≤` excludes the trivial flower tree, whose term is the identity of
  `𝒳 = 1 + ∑ 𝒥̃` (F39; DH23 (kernelexp)).
- `Y`: (Y-1) order `> N_{p+1}`, (Y-2) each child of the root has `≤ N_{p+1}` below it.
- `W`: (W-1) order `> N_{p+1}`, (W-2) each sibling of `𝔣` has `≤ N_{p+1}` below it, (W-3) order minus the
  count below `𝔣^pr` `≤ N_{p+1}`.

For `Y` and `W` these replace the bound `N_{p+1}` of `ℋ^tr` (F46, delta-1 D1). -/
def FlowerKindOK (p Ntr : ℕ) : FlowerKind → Prop
  | .X => ∀ j, 1 ≤ LG.topOrder p j ∧ LG.topOrder p j ≤ Ntr
  | .Y => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr
  | .W => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1.1 = j →
      LG.garden.IsFlowerParent b →
        (∀ i : Fin 3, ¬ LG.IsFlowerNode (b.child i) → LG.topCountBelow p (b.child i) ≤ Ntr) ∧
        LG.topOrder p j - LG.topCountBelow p b.toNode ≤ Ntr

end LayeredGarden
end WaveTurbulence
