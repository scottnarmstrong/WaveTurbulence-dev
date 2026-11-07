/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideSimpleAtoms
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideSpecialBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectPotential
import Mathlib.Tactic

/-! # Exact component additivity of both run-accounting resources -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem balancedPotential_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    balancedPotential M = balancedPotential (appbSideMolecule M S hS)+
      balancedPotential (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  have h3 := degreeAtoms_card_closed_side_add M S hS 3
  have hν := nu_closed_side_add M S hS
  have h2 := simpleDegreeTwoAtoms_card_closed_side_add M S hS
  have hξ := specialBonds_card_closed_side_add M S hS
  unfold balancedPotential
  omega

theorem defectPotential_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    defectPotential M = defectPotential (appbSideMolecule M S hS)+
      defectPotential (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  have h3 := degreeAtoms_card_closed_side_add M S hS 3
  have hν := nu_closed_side_add M S hS
  unfold defectPotential
  omega

end WaveTurbulence.Mole.AppbAlgorithm
