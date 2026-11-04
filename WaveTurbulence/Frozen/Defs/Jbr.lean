/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# jbr

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The Japanese bracket `⟨k⟩ = (1 + |k|²)^{1/2}`. -/
noncomputable def jbr {d : ℕ} (k : Mom d) : ℝ := Real.sqrt (1 + ‖k‖ ^ 2)

end WaveTurbulence
