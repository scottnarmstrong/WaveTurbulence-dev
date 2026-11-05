/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Counts of actual vines via the exact B2 realization (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The pinned undirected realization preserves the number of atoms and
bonds, including all multiplicities. -/
theorem isVine_counts {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : ∃ k : List ℕ, k.length=X.template.slots.length ∧
    S.card=X.template.n+2*k.sum ∧ (M.groupBonds S).card=X.template.bonds.length+4*k.sum := by
  obtain ⟨hB,k,hk,f,hf,himage,_hj,he⟩ := h
  have hc := congrArg Finset.card himage
  rw [Finset.card_image_of_injOn hf,Finset.card_range,expand_atoms_exact X k hk] at hc
  have hb := congrArg Multiset.card he
  simp only [Multiset.card_map,Multiset.coe_card,List.length_map] at hb
  rw [expand_bonds X k hk] at hb
  exact ⟨k,hk,hc,hb⟩

/-- Every vine has E=2V-2, without a connectivity or orientation assumption
beyond the exact pinned vine predicate. -/
theorem isVine_bond_atom_count {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : (M.groupBonds S).card+2=2*S.card := by
  obtain ⟨k,_hk,hc,hb⟩ := isVine_counts h
  have ht := template_bond_count X
  omega

/-- Actual vine joints have degree two within the vine. -/
theorem isVine_joint_degrees {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : M.degIn S a=2 ∧ M.degIn S b=2 :=
  Mole.block_joint_degrees M h.1

end WaveTurbulence.Vine
