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

end WaveTurbulence.Vine
