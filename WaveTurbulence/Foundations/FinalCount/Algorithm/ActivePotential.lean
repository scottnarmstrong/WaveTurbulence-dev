/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.LinkPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DefectAtom
import Mathlib.Tactic

/-! # The active link potential vanishes at the algorithm's terminal graph -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def activeLinkPotential (M : Molecule V D) : ℤ :=
  linkPotential M-(appbDegreeAtoms M 0).card

theorem activeLinkPotential_terminal (M : Molecule V D) (h : M.bonds = ∅) : activeLinkPotential M = 0 := by
  have hiso : appbDegreeAtoms M 0 = M.atoms := by
    ext a
    simp only [appbDegreeAtoms,mem_filter,degree_zero_of_no_bonds M h,and_true]
  unfold activeLinkPotential linkPotential
  rw [links_empty_of_no_bonds M h,hiso,card_empty]
  omega

theorem no_isolated_atoms_of_connected_nontrivial (M : Molecule V D)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hne : M.bonds.Nonempty) :
    appbDegreeAtoms M 0 = ∅ := by
  classical
  obtain ⟨e,he⟩ := hne
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨ha,hd⟩ := mem_filter.mp ha
  have hEq := eq_of_sameComponent_of_degree_zero M (hc (M.atom e) (M.atom_mem e) a ha) hd
  have hp : 0 < M.deg (M.atom e) := card_pos.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  rw [hEq,hd] at hp
  omega

theorem sourceRho_le_active_initial (M : Molecule V D) (hM : M.IsMolecule)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hne : M.bonds.Nonempty) :
    (sourceRho M : ℤ) ≤ activeLinkPotential M := by
  unfold activeLinkPotential
  rw [no_isolated_atoms_of_connected_nontrivial M hc hne,card_empty,Nat.cast_zero,sub_zero]
  exact (sourceRho_le_linkPotential M hM).1

end WaveTurbulence.Mole.AppbAlgorithm
