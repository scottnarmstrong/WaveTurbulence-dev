/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTripleStripGood
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameConservation
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
import Mathlib.Tactic

/-! # The inverse-weight gain on an actual triple meeting a two-atom cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_triple_permutation_encoding_apply_good {K : Type*} (π : Equiv.Perm (Fin 3))
    (q : Fin 3 → K) (j : Fin 3) : ![q (π 0),q (π 1),q (π 2)] j = q (π j) := by
  fin_cases j <;> rfl

end WaveTurbulence.Mole
