/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsGamma1

/-!
# regBound

Wave B tier B2 (WaveB2-Statements.lean), source: (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The bound `C₁ (C₁δ)^n L^{-(γ₁ - √η) g}` of B2.1/B2.2. -/
noncomputable def regBound (P : WTParams) (n g : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g))

end WaveTurbulence
