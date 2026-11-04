/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopCountBelow
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopOrder
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TreeKind

/-!
# LayeredGarden.TreeKindOK

Wave B tier B1 (WaveB1-Flower.lean), source: T L2312. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **The kind restrictions on the trees of a couple:**
- `tr`: top order `≤ N_{p+1}` (`a^tr`);
- `L0`: top order `> N_{p+1}`, and each child of the root has `≤ N_{p+1}` below it (`ℒ₀`, T L2312). -/
def TreeKindOK (p Ntr : ℕ) : TreeKind → Prop
  | .tr => ∀ j, LG.topOrder p j ≤ Ntr
  | .L0 => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr

end LayeredGarden
end WaveTurbulence
