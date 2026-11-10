/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveSourceEquations
import Mathlib.Tactic

/-! # Removing the genuinely fixed extra label from the old source equations -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem fixed_extra_signed_momentum {E : Type*} [AddCommGroup E]
    (sx sy sr : Bool) (a b : E) (k : Fin 5 → E)
    (h : SignedDoubleFiveMomentum sx sy sr a b k) :
    SignedDoublePairMomentum sx sy sr a
      (b-doubleSign (doubleExtraSign sx sy sr) • k 4) ![k 0,k 1,k 2,k 3] := by
  constructor
  · exact h.1
  · change -(doubleSign sx • k 0)-doubleSign sy • k 1-doubleSign sr • k 3 = _
    rw [← h.2]
    abel

end WaveTurbulence.MoleProp
