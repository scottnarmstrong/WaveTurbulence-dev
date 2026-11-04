/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.MarkTag
public import WaveTurbulence.Frozen.Defs.SymmPairs
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.MatchesPairedTree

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- A paired-tree carrier `G` has the tree `T`, lone leaf at `lp` (marked `lower`) and the other leaf
pairs of the list `P`. -/
def Garden.MatchesPairedTree (G : Garden 1) (T : TTree) (lp : Path)
    (P : List ((Fin 1 × Path) × (Fin 1 × Path))) : Prop :=
  G.tree 0 = T ∧ (∀ ℓ : GLeaf G.tree, G.mark ℓ = if ℓ.1.2 = lp then some .lower else none) ∧
    ∀ ℓ : GLeaf G.tree, ℓ.1.2 ≠ lp → (ℓ.1, (G.pair ℓ).1) ∈ symmPairs P

end WaveTurbulence
