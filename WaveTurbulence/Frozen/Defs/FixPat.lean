/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# FixPat

Wave B tier B1 (WaveB1-Flower.lean), source: T L2312. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The **fixed-time pattern** of one flower tree (T L2312, L2331). In every pattern the flower parent
has time `s`.
- `plain`: no other designated node.
- `dRoot`: the root also has time `t` (`∂_t`).
- `dParent`: the parent of `𝔣^pr` also has time `s` (`∂_s`).
- `dChild i`: the `i`-th child of `𝔣^pr`, a branching node, also has time `s` (`∂_s`). -/
inductive FixPat : Type
  | plain : FixPat
  | dRoot : FixPat
  | dParent : FixPat
  | dChild (i : Fin 3) : FixPat

end WaveTurbulence
