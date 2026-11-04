/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCodeLone
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RegChain.lonePath

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The path of the lone leaf of a chain (from its root `𝔫_1`). -/
def RegChain.lonePath : RegChain → Path
  | .nil => []
  | .pair m _ _ inner rest => [m.c] ++ inner.lonePath ++ [m.lone] ++ rest.lonePath

end WaveTurbulence
