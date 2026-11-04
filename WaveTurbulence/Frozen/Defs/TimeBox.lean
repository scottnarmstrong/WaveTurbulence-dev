/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# timeBox

Wave B tier B2 (WaveB2-Statements.lean), source: (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The time box `ℬ = [q, q+1] × [q', q'+1]` of pairs `(t, s)`. -/
def timeBox (q q' : ℝ) : Set (Fin 2 → ℝ) := {ts | ts 0 ∈ Icc q (q + 1) ∧ ts 1 ∈ Icc q' (q' + 1)}

end WaveTurbulence
