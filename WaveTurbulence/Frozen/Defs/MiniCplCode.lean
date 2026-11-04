/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# MiniCplCode

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`; WAVE-B §3.1. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The code of a `(1,1)`-mini-couple (T Def `defreg`, Figure `MiniCpl.png`; WAVE-B §3.1): `0` is code
`00` (straight: `L⁺ ↔ L⁻`, `R⁺ ↔ R⁻`), `1` is code `01` (crossed: `L⁺ ↔ R⁻`, `R⁺ ↔ L⁻`); always
`M⁺ ↔ M⁻`. Colours: red, green, blue = the pairs containing `L⁺`, `M⁺`, `R⁺` (first tree = the `+`
tree, figure-defs M1). -/
abbrev MiniCplCode := Fin 2

end WaveTurbulence
