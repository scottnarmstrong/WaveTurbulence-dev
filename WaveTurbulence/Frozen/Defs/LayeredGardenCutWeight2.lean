/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.DyadicCut
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenInstDecidableOnStem
public import WaveTurbulence.Frozen.Defs.LayeredGardenOnStem
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.OmegaNode
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.cutWeight2

Wave B tier B1 (WaveB1-Flower.lean), source: T L2285. Frozen by ruling D7
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
/-- The `M₂` weight (T L2285, L2299): per tree, `φ_{M₂}` of the largest `|Ω_𝔫|` over the stem branching
nodes other than `𝔣^pr`. -/
noncomputable def cutWeight2 (L : ℝ) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₂ (((Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b).sup
      fun b => ‖omegaNode LG.garden k b‖₊ : NNReal) : ℝ)

end LayeredGarden
end WaveTurbulence
