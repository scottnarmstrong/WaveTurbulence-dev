/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# partialMom

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- The coordinate partial derivative `∂_{k^j} F` on `ℝ^d`. -/
noncomputable def partialMom (j : Fin d) (F : Mom d → ℂ) : Mom d → ℂ :=
  fun k => fderiv ℝ F k (EuclideanSpace.single j 1)

end Norms
end WaveTurbulence
