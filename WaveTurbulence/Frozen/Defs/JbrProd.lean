/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# jbrProd

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- `∏_j ⟨n_j/L⟩`. -/
noncomputable def jbrProd {w d : ℕ} (L : ℝ) (n : Fin w → (Fin d → ℤ)) : ℝ :=
  ∏ j, jbr (latticePoint L (n j))

end WaveTurbulence
