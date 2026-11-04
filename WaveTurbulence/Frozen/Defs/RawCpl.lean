/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# RawCpl

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- **Raw couple data**: the `+` tree, the `-` tree, and the leaf pairs as `(+ leaf, - leaf)` addresses
(tree `0` = `𝒯⁺`, tree `1` = `𝒯⁻`). -/
abbrev RawCpl := (TTree × TTree) × List ((Fin 2 × Path) × (Fin 2 × Path))

end WaveTurbulence
