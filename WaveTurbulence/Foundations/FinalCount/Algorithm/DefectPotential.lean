/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.InitialStatistics
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
import Mathlib.Tactic

/-! # The V3-minus-nu resource that forces a good operation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def defectPotential (M : Molecule V D) : ℤ :=
  ((appbDegreeAtoms M 3).card : ℤ)-appbNu M

theorem defectPotential_pos_of_nu_neg (M : Molecule V D) (hnu : appbNu M < 0) :
    0 < defectPotential M := by
  unfold defectPotential
  omega

theorem nu_zero_of_no_bonds (M : Molecule V D) (h : M.bonds = ∅) : appbNu M = 0 := by
  unfold appbNu
  rw [h,card_empty,components_eq_atoms_of_no_bonds M h]
  push_cast
  ring

theorem defectPotential_zero_terminal (M : Molecule V D) (h : M.bonds = ∅) : defectPotential M = 0 := by
  have h3 : appbDegreeAtoms M 3 = ∅ := by
    ext a
    simp only [appbDegreeAtoms,mem_filter,degree_zero_of_no_bonds M h,
      Nat.reduceEqDiff,and_false,notMem_empty]
  unfold defectPotential
  rw [h3,card_empty,nu_zero_of_no_bonds M h]
  rfl

end WaveTurbulence.Mole.AppbAlgorithm
