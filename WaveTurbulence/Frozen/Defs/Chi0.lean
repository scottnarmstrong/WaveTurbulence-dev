/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# chi0

Wave B tier B1 (WaveB1-System.lean), source: T L617–L623. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **The cutoff `χ₀`** (T L617–L623), one explicit formula: `χ₀(x) = ψ(2 - 2|x|)` with `ψ` Mathlib's
`Real.smoothTransition` (built from `e^{-1/x}`): even, `C^∞`, `[0,1]`-valued, `= 1` on `[-1/2, 1/2]`,
`= 0` off `(-1, 1)`. -/
noncomputable def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * |x|)

end WaveTurbulence
