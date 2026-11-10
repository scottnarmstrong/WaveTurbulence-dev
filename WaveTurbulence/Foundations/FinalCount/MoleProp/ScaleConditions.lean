/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
import Mathlib.Tactic

/-! # Literal large-gap and per-position scale restrictions for DH23 10.1

The unit endpoint has only a lower gap comparison; large gaps are not
truncated physically. Zero scales mean actual zero gap, independently of
large gaps at opposite darts of one atom.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- The source convention |r|∼₀P, with comparability factor 2. -/
def GapScale (L P r : ℝ) : Prop :=
  (P = 0 ∧ r = 0) ∨
  (L⁻¹ ≤ P ∧ P < 1 ∧ P / 2 ≤ r ∧ r ≤ 2 * P) ∨
  (P = 1 ∧ 1 / 2 ≤ r)

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

end WaveTurbulence.MoleProp
