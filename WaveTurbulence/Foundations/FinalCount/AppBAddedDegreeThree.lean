/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDegreeCountTransport
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Exact degree-three count under distinct-endpoint bond insertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_addBond_degreeThree_difference (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b) :
    ((appbDegreeAtoms (addBond M a b) 3).card : ℤ)-(appbDegreeAtoms M 3).card =
      ((if M.deg a = 2 then (1 : ℤ) else 0)-(if M.deg a = 3 then 1 else 0))+
      ((if M.deg b = 2 then (1 : ℤ) else 0)-(if M.deg b = 3 then 1 else 0)) := by
  classical
  have hatoms : (addBond M a b).atoms = M.atoms := by
    change insert a (insert b M.atoms) = M.atoms
    simp only [insert_eq_of_mem ha,insert_eq_of_mem hb]
  have hsub : ({a,b} : Finset V) ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    · exact (mem_singleton.mp hv) ▸ hb
  have hdeg : ∀ v ∈ M.atoms,v ∉ ({a,b} : Finset V) → (addBond M a b).deg v = M.deg v := by
    intro v hv hn
    have ha' : a ≠ v := by intro he; exact hn (he ▸ mem_insert_self _ _)
    have hb' : b ≠ v := by intro he; exact hn (he ▸ mem_insert_of_mem (mem_singleton_self _))
    simp only [addBond_deg,ha',hb',ite_false,add_zero]
  have hda : (addBond M a b).deg a = 3 ↔ M.deg a = 2 := by
    simp only [addBond_deg,hab.symm,ite_false,ite_true,add_zero]
    omega
  have hdb : (addBond M a b).deg b = 3 ↔ M.deg b = 2 := by
    simp only [addBond_deg,hab,ite_false,ite_true,add_zero]
    omega
  rw [appb_degreeCount_difference_of_local_change M (addBond M a b) hatoms {a,b} hsub hdeg 3]
  simp only [sum_insert,mem_singleton,hab,not_false_eq_true,sum_singleton,hda,hdb]

end WaveTurbulence.Mole
