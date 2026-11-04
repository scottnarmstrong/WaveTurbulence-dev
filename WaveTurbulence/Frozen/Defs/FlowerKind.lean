/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# FlowerKind

Wave B tier B1 (WaveB1-Flower.lean), source: T (operatorxker); T L2273. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The kinds of initial flower trees: `𝒳` (T (operatorxker), without the identity term), `𝒴` and `𝒲`
(T L2273). -/
inductive FlowerKind : Type
  | X : FlowerKind
  | Y : FlowerKind
  | W : FlowerKind

end WaveTurbulence
