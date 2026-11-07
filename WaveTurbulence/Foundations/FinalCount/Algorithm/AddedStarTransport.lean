/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoLocalEdit
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
import Mathlib.Tactic

/-! # Insertion preserves old stars away from its two endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem addBond_atoms_of_mem (M : Molecule V D) {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) :
    (addBond M a b).atoms = M.atoms := by
  change insert a (insert b M.atoms) = M.atoms
  rw [insert_eq_of_mem hb,insert_eq_of_mem ha]

theorem addBond_bondsBetween_of_remote (M : Molecule V D) (a b : V) {u : V}
    (ha : a ≠ u) (hb : b ≠ u) (v : V) :
    (addBond M a b).bondsBetween u v = M.bondsBetween u v := by
  classical
  rw [appb_addBond_bondsBetween]
  have hn : s(a,b) ≠ s(u,v) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact ha h.1
    · exact hb h.2
  simp only [hn,ite_false,add_zero]

theorem addBond_simpleDegreeTwo_iff_of_remote (M : Molecule V D) {a b u : V}
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hau : a ≠ u) (hbu : b ≠ u) :
    SimpleDegreeTwo (addBond M a b) u ↔ SimpleDegreeTwo M u := by
  simp only [SimpleDegreeTwo,addBond_deg,hau,hbu,ite_false,add_zero,
    addBond_atoms_of_mem M ha hb,addBond_bondsBetween_of_remote M a b hau hbu]

theorem insertion_simple_count_change_abs_le_two (M : Molecule V D) {a b : V}
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b) :
    |((simpleDegreeTwoAtoms (addBond M a b)).card : ℤ)-(simpleDegreeTwoAtoms M).card| ≤ 2 := by
  classical
  have hS : ({a,b} : Finset V) ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    · exact mem_singleton.mp hv ▸ hb
  have hout : ∀ v ∈ M.atoms,v ∉ ({a,b} : Finset V) →
      (SimpleDegreeTwo (addBond M a b) v ↔ SimpleDegreeTwo M v) := by
    intro v hv hn
    have ha' : a ≠ v := by intro he; exact hn (by simp [he])
    have hb' : b ≠ v := by intro he; exact hn (by simp [he])
    exact addBond_simpleDegreeTwo_iff_of_remote M ha hb ha' hb'
  have hh := simpleDegreeTwo_local_edit_abs_le M (addBond M a b) (addBond_atoms_of_mem M ha hb) _ hS hout
  simpa only [card_pair hab,Nat.cast_ofNat] using hh

end WaveTurbulence.Mole.AppbAlgorithm
