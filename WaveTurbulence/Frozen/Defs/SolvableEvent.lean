/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.PartialDeriv
public import WaveTurbulence.Frozen.Defs.NormLaplacian
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.InitialCoeff

/-!
# SolvableEvent

Deng–Hani, L316, L818. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The event that (NLS) with data (DAT) has a smooth solution on `[0, T]`. -/
def solvableEvent {d : ℕ} {Ω : Type*} (L α T : ℝ) (φin : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) : Set Ω :=
  {ω | ∃ u, IsSmoothNLSSolution L α T (initialCoeff L φin g ω) u}

end WaveTurbulence
