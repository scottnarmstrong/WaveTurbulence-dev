/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Uniform nu cost of one actual atom deletion in a disconnected molecule -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem singleton_nu_change_abs_le (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} (hv : v ∈ M.atoms) :
    |appbNu (Degen.eraseAtoms M {v})-appbNu M| ≤ 16 := by
  have hV := Degen.card_atoms_erase_singleton_add_one M hv
  have hE := Degen.card_bonds_erase_singleton_add_incident M v
  have hF := MoleProp.numComponents_erase_singleton_add_one M hv
  have hVZ : ((Degen.eraseAtoms M {v}).atoms.card : ℤ)+1 = M.atoms.card := by exact_mod_cast hV
  have hEZ : ((Degen.eraseAtoms M {v}).bonds.card : ℤ)+(Degen.incidentBondsAt M v).card = M.bonds.card := by exact_mod_cast hE
  have hFZ : ((Degen.eraseAtoms M {v}).numComponents : ℤ)+1 = M.numComponents+(Degen.newComponents M {v}).card := by exact_mod_cast hF
  have hI := Degen.card_incident_add_self_eq_deg M v
  have hB := Degen.card_boundary_add_twice_self_eq_deg M v
  have hN := Degen.card_newComponents_le_boundary M {v}
  have hcap := deg_le_four M hM hv
  have hi : (Degen.incidentBondsAt M v).card ≤ 4 := by omega
  have hn : (Degen.newComponents M {v}).card ≤ 4 := by omega
  unfold appbNu
  apply abs_le.mpr
  constructor <;> omega

end WaveTurbulence.Mole.AppbAlgorithm
