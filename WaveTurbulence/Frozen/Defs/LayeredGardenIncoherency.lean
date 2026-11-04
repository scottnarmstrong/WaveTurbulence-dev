/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.incoherency

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defcoh`, L885–L887. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **The incoherency index** (T Def `defcoh`, L885–L887) of a layering w.r.t. a list of links: the
number of links `(𝔫, 𝔫')` with `𝔏_𝔫 ≠ 𝔏_𝔫'`. Coherent: index `0`. -/
def LayeredGarden.incoherency {w : ℕ} (LG : LayeredGarden w)
    (links : List ((Fin w × Path) × (Fin w × Path))) : ℕ :=
  ((Finset.univ : Finset (GBranch LG.garden.tree × GBranch LG.garden.tree)).filter fun bb =>
    (bb.1.1, bb.2.1) ∈ links ∧ LG.layer bb.1.toNode ≠ LG.layer bb.2.toNode).card

end WaveTurbulence
