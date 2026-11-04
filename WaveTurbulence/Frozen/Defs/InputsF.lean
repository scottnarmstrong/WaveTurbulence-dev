/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams

/-!
# inputsF

Wave B tier B1 (WaveB1-System.lean), source: T (ansatz3), L703. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The input functions `F_q = φ(δq) + R_q` (T (ansatz3), L703). -/
noncomputable def inputsF (P : WTParams) (R : ℕ → Mom P.d → ℝ) : ℕ → Mom P.d → ℝ :=
  fun q k => P.φ (P.δ * q) k + R q k

end WaveTurbulence
