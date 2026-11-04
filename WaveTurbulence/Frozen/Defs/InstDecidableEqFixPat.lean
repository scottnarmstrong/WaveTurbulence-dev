/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FixPatDecEq

/-!
# instDecidableEqFixPat

Wave B tier B1 (WaveB1-Flower.lean), source: — (DecidableEq instance for `FixPat`; no source object). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

@[instance_reducible, instance] def instDecidableEqFixPat : DecidableEq FixPat := FixPat.decEq

end WaveTurbulence
