/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Chi0

/-!
# dyadicCut

Wave B tier B1 (WaveB1-Flower.lean), source: T L2283–L2285. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The dyadic smooth cutoffs `φ_M`, `M = 2^j L`, behind "`∼₀ M` (or `≲₀ M` if `M = L`)" (T L2283–L2285):
- `φ_L(x) = χ₀(x/L)`;
- `φ_{2^jL}(x) = χ₀(x/(2^jL)) − χ₀(x/(2^{j−1}L))` for `j ≥ 1`.

They sum to `1`. `φ_M` is supported in `|x| < M`, and in `|x| > M/4` when `j ≥ 1`. -/
noncomputable def dyadicCut (L : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then chi0 (x / L) else chi0 (x / (2 ^ j * L)) - chi0 (x / (2 ^ (j - 1) * L))

end WaveTurbulence
