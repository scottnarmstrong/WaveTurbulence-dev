/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.DyadicCut
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGNode
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsFlowerNode
public import WaveTurbulence.Frozen.Defs.LayeredGardenIsTopLeaf
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.cutWeight1

Wave B tier B1 (WaveB1-Flower.lean), source: T L2283. Frozen by ruling D7
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
/-- The `M₁` weight (T L2283, L2294): per tree, `φ_{M₁}` of the largest `|k|` over the non-flower
leaves of the initial flower tree. -/
noncomputable def cutWeight1 (p : ℕ) (L : ℝ) (j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₁ (((Finset.univ.filter fun a : GNode LG.garden.tree =>
    a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a).sup fun a => ‖k a‖₊ : NNReal) : ℝ)

end LayeredGarden
end WaveTurbulence
