/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Initial degree deficits and nu in DH23 Proposition 10.2

Edge/vertex equalities are stated over integers to avoid natural-subtraction
artifacts at an empty graph. The source input is connected, by §10.1.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def degreeDeficit (M : Molecule V D) : ℕ := ∑ v ∈ M.atoms,(4-M.deg v)

theorem degree_sum_add_deficit (M : Molecule V D) (hM : M.IsMolecule) :
    2*M.bonds.card+degreeDeficit M = 4*M.atoms.card := by
  rw [← sum_degrees_eq_two_mul_bonds]
  unfold degreeDeficit
  rw [← sum_add_distrib]
  have hh : (∑ v ∈ M.atoms,(M.deg v+(4-M.deg v))) = ∑ _v ∈ M.atoms,(4 : ℕ) := by
    apply sum_congr rfl
    intro v hv
    exact Nat.add_sub_of_le (deg_le_four M hM hv)
  rw [hh]
  simp only [sum_const,smul_eq_mul]
  omega

theorem degreeThree_le_deficit (M : Molecule V D) :
    (appbDegreeAtoms M 3).card ≤ degreeDeficit M := by
  classical
  have he : (appbDegreeAtoms M 3).card = ∑ v ∈ M.atoms,if M.deg v = 3 then (1 : ℕ) else 0 := by
    simp only [appbDegreeAtoms,Finset.sum_boole,Nat.cast_id]
  rw [he]
  unfold degreeDeficit
  apply sum_le_sum
  intro v hv
  split_ifs with hd
  · rw [hd]
  · exact Nat.zero_le _

theorem odd_initial_statistics (M : Molecule V D) (hM : M.IsMolecule)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hE : (M.bonds.card : ℤ) = 2*(M.atoms.card : ℤ)-1) :
    degreeDeficit M = 2 ∧ appbNu M = -2 ∧ (appbDegreeAtoms M 3).card ≤ 2 := by
  have hV : M.atoms.Nonempty := card_pos.mp (by omega)
  have hF := numComponents_eq_one M hV hc
  have hh := degree_sum_add_deficit M hM
  have hd : degreeDeficit M = 2 := by omega
  refine ⟨hd,?_,(degreeThree_le_deficit M).trans_eq hd⟩
  unfold appbNu
  rw [hF,hE]
  ring

theorem even_initial_statistics (M : Molecule V D) (hM : M.IsMolecule)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hE : (M.bonds.card : ℤ) = 2*(M.atoms.card : ℤ)-2) :
    degreeDeficit M = 4 ∧ appbNu M = 0 ∧ (appbDegreeAtoms M 3).card ≤ 4 := by
  have hV : M.atoms.Nonempty := card_pos.mp (by omega)
  have hF := numComponents_eq_one M hV hc
  have hh := degree_sum_add_deficit M hM
  have hd : degreeDeficit M = 4 := by omega
  refine ⟨hd,?_,(degreeThree_le_deficit M).trans_eq hd⟩
  unfold appbNu
  rw [hF,hE]
  ring

end WaveTurbulence.Mole.AppbAlgorithm
