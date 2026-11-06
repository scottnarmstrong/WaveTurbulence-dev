/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ProdDyadicCut
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
# LayeredGarden.cutWeight2P

Wave B tier B1 (flower cutoff successor, R62), source: T L2285; DH21 L2735. Frozen by ruling D13
(`docs/DECISIONS.md#D13`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)
variable {d : ℕ}

open Classical in
/-- The `M₂` weight, product form (T L2285, L2299; DH21 L2735): per tree, `Ψ_{j₂}` of the `|Ω_𝔫|` over the
stem branching nodes other than `𝔣^pr`. -/
noncomputable def cutWeight2P (L : ℝ) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, prodDyadicCut L j₂ (Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b)
      (fun b => |omegaNode LG.garden k b|)

end LayeredGarden
end WaveTurbulence
