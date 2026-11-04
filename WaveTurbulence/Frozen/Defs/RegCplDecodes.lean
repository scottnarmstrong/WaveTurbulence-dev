/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenMatchesCouple
public import WaveTurbulence.Frozen.Defs.RegCplRaw
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplTreesRegChainPlug
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RegCpl.Decodes

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- `Q` is the structure data of the couple carrier `G`. -/
def RegCpl.Decodes (Q : RegCpl) (G : Garden 2) : Prop := G.MatchesCouple Q.trees Q.raw.2

end WaveTurbulence
