/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniCplCode
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# RegChain.isNil

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- Is the chain empty? -/
def RegChain.isNil : RegChain → Bool
  | .nil => true
  | _ => false

end WaveTurbulence
