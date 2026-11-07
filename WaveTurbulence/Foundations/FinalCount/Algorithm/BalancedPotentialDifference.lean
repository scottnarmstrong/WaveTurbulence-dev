/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotential
import Mathlib.Tactic

/-! # Exact signed increment of the scalar source resource -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem balancedPotential_difference (M : Molecule V D) (N : Molecule V E) :
    balancedPotential N-balancedPotential M =
      100*((((appbDegreeAtoms N 3).card : ℤ)-(appbDegreeAtoms M 3).card)-(appbNu N-appbNu M))+
      (appbNu N-appbNu M)+
      4*((((simpleDegreeTwoAtoms N).card : ℤ)-(simpleDegreeTwoAtoms M).card)-
        (((appbSpecialBonds N).card : ℤ)-(appbSpecialBonds M).card)) := by
  unfold balancedPotential
  ring

end WaveTurbulence.Mole.AppbAlgorithm
