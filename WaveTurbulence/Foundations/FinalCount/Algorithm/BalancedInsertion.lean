/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotentialDifference
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewSpecialInsertion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeThreeChangeBound
public import WaveTurbulence.Foundations.FinalCount.AppBAddConnectedBond
import Mathlib.Tactic

/-! # Uniform resource cost of reinserting inside the source component -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem same_component_insertion_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hconn : M.SameComponent a b) :
    balancedPotential M-50 ≤ balancedPotential (addBond M a b) := by
  have hA := addBond_atoms_of_mem M ha hb
  have hF := appb_addBond_components_of_connected M a b ha hb hconn
  have hE := addBond_card_bonds M a b
  have hnu : appbNu (addBond M a b)-appbNu M = -2 := by
    unfold appbNu
    rw [hA,hF,hE]
    push_cast
    ring
  have h3 := (abs_le.mp (insertion_degreeThree_change_abs_le M a b ha hb hab)).1
  have h2 := (abs_le.mp (insertion_simple_count_change_abs_le_two M ha hb hab)).1
  have hS := insertion_special_count_le_old_add_nine M hM ha hb hab
  have hSz : ((appbSpecialBonds (addBond M a b)).card : ℤ) ≤ (appbSpecialBonds M).card+9 := by exact_mod_cast hS
  have hΔ := balancedPotential_difference M (addBond M a b)
  omega

end WaveTurbulence.Mole.AppbAlgorithm
