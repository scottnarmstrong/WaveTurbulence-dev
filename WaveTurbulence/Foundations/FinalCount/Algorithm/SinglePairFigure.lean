/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairPatterns
import Mathlib.Tactic

/-! # The geometric alternatives of source rule two -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A primary 3S3 figure or one of the six new figures. -/
def SinglePairFigure (M : Molecule V D) : Prop :=
  ∃ k ∈ ([AppbPatternKind.s33,.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _),
    Nonempty (AppbRealization M k.pattern)

end WaveTurbulence.Mole.AppbAlgorithm
