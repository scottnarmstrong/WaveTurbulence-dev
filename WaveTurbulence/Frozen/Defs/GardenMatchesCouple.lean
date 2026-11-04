/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.IsCouple
public import WaveTurbulence.Frozen.Defs.SymmPairs
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden.MatchesCouple

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- A couple carrier `G` has the trees `T = (𝒯⁺, 𝒯⁻)` and the leaf pairs of the list `P` (unordered). -/
def Garden.MatchesCouple (G : Garden 2) (T : TTree × TTree)
    (P : List ((Fin 2 × Path) × (Fin 2 × Path))) : Prop :=
  IsCouple G ∧ G.tree 0 = T.1 ∧ G.tree 1 = T.2 ∧
    ∀ ℓ : GLeaf G.tree, (ℓ.1, (G.pair ℓ).1) ∈ symmPairs P

end WaveTurbulence
