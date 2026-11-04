/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TruncSumC
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm

/-!
# coupleRemainder

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- The couple remainder of (estcouple): `k ↦ 𝒦^tr_{p+1,N}(t; k) - [N even] 𝒰^{(p)}_{N/2}(t, k)`. -/
noncomputable def coupleRemainder (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) :
    Mom P.d → ℂ := fun k =>
  truncSumC P (inputsF P R) (p + 1) N t k -
    (if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0)

end WaveTurbulence
