/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Chi0

/-!
# prodDyadicCut

Wave B tier B1 (flower cutoff successor, R62), source: T L2283–L2285; DH21 L2731. Frozen by ruling D13
(`docs/DECISIONS.md#D13`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **Product-form dyadic cutoff** (T L2283, L2285 "by a smooth cutoff function"; DH21 L2731): a dyadic
partition per entry, cut at the largest index: `Ψ_0 = ∏_a χ₀(y_a/L)`,
`Ψ_j = ∏_a χ₀(y_a/(2^j L)) − ∏_a χ₀(y_a/(2^{j−1} L))`. For `L > 0` and `y ≥ 0` they sum to `1`, and
`Ψ_j ≠ 0` forces every `y_a < 2^j L` and, for `j ≥ 1`, some `y_a > 2^j L / 4`. On a singleton
`Ψ_j = dyadicCut L j`; on `∅`, `Ψ_0 = 1` and `Ψ_j = 0` (`j ≥ 1`). -/
noncomputable def prodDyadicCut {ι : Type*} (L : ℝ) (j : ℕ) (s : Finset ι) (y : ι → ℝ) : ℝ :=
  if j = 0 then ∏ a ∈ s, chi0 (y a / L)
  else ∏ a ∈ s, chi0 (y a / (2 ^ j * L)) - ∏ a ∈ s, chi0 (y a / (2 ^ (j - 1) * L))

end WaveTurbulence
