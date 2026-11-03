/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# InitialCoeff

Deng–Hani, L290-L293 (DAT). Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The Fourier coefficients `û_in(k) = √(φin(k)) g_k` of the random initial datum (DAT). -/
def initialCoeff {d : ℕ} {Ω : Type*} (L : ℝ) (φin : Mom d → ℝ) (g : (Fin d → ℤ) → Ω → ℂ)
    (ω : Ω) (n : Fin d → ℤ) : ℂ :=
  (Real.sqrt (φin (latticePoint L n)) : ℂ) * g n ω

end WaveTurbulence
