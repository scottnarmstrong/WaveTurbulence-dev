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
# ZNorm

Wave B tier B1 (WaveB1-System.lean), source: T L787. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- `‖b‖_Z` for `b` on `[p, p+1]`, `Z = Z^Λ([p,p+1])` (T L787). -/
noncomputable def ZNorm (L : ℝ) (Λ : ℝ) {p : ℕ} (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) :
    ℝ≥0∞ :=
  ⨆ (t : Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ), ENNReal.ofReal (jbr (latticePoint L n) ^ Λ * ‖b t n‖)

end Norms
end WaveTurbulence
