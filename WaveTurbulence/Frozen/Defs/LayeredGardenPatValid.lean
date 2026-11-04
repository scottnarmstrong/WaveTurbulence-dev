/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchIsChildOf
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.PatValid

Wave B tier B1 (WaveB1-Flower.lean), source: T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The pattern of tree `j` designates an existing node other than `𝔣^pr`. Without it the pattern's
boundary term does not exist.

For `dChild i` the designated child of `𝔣^pr` is in layer `p` (F68). The boundary term `δ(t_𝔫 − s)` of `∂_s`
(T L2331) is taken in the single-tree kernel `𝒥^†`, where a non-flower child of `𝔣^pr` is a top-layer branching
node or a leaf. So the root of an attached lower-layer garden is excluded. -/
def PatValid (p : ℕ) (j : Fin w) : FixPat → Prop
  | .plain => True
  | .dRoot => ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ ¬ LG.garden.IsFlowerParent b
  | .dParent => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧ c.IsChildOf b
  | .dChild i => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧
      b.1.1 = j ∧ b.1.2 = c.1.2 ++ [i] ∧ LG.layer b.toNode = p

end LayeredGarden
end WaveTurbulence
