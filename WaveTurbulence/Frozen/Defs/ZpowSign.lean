/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# zpowSign

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- `z^ζ`: `z^+ = z`, `z^- = z̄` (T §2.4.3 notations). -/
noncomputable def zpowSign (ζ : ℤˣ) (z : ℂ) : ℂ := if ζ = 1 then z else (starRingEnd ℂ) z

end WaveTurbulence
