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
# ZNormOn

Wave B tier B1 (WaveB1-System.lean), source: T (defznorm), L594. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- **`‖a‖_{Z^Λ(ℬ)}`** (T (defznorm), L594) of a lattice array depending on time. -/
noncomputable def ZNormOn (L : ℝ) (Λ : ℝ) (B : Set ℝ) (a : ℝ → (Fin d → ℤ) → ℂ) : ℝ≥0∞ :=
  ⨆ (t ∈ B) (n : Fin d → ℤ), ENNReal.ofReal (jbr (latticePoint L n) ^ Λ * ‖a t n‖)

end Norms
end WaveTurbulence
