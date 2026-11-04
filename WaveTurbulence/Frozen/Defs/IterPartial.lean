/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.PartialMom

/-!
# iterPartial

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- `∂^ρ F` for a multi-index `ρ : Fin d → ℕ`. -/
noncomputable def iterPartial (ρ : Fin d → ℕ) (F : Mom d → ℂ) : Mom d → ℂ :=
  (List.finRange d).foldr (fun j G => (partialMom j)^[ρ j] G) F

end Norms
end WaveTurbulence
