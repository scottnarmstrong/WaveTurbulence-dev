/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenMatchesPairedTree
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegCplPairsAtRegChainPairsAt
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplTreesRegChainPlug
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RegChain.DecodesTree

Wave B tier B2 (WaveB2-Regular.lean), source: T Prop `propstructure`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **Codes of regular trees** (T Prop `propstructure`, last part): a regular tree is coded by its
regular chain `𝒳₀` with couples `𝒬_{j,0,ι}` (`nil` = the trivial tree `•`); the sign is that of the
carrier. `X` is the structure data of the paired-tree carrier `G`. -/
def RegChain.DecodesTree (X : RegChain) (G : Garden 1) : Prop :=
  G.MatchesPairedTree (X.plug (G.sig 0) .leaf) X.lonePath (X.pairsAt (G.sig 0) (0, []))

end WaveTurbulence
