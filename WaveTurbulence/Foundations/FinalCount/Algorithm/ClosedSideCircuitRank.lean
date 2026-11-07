/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideComponents
import Mathlib.Tactic

/-! # Atom, bond and circuit-rank additivity over closed sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bonds_closed_side_image (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbSideMolecule M S hS).bonds.image Subtype.val = M.bonds.filter (fun x => M.atom x ∈ S) := by
  ext x
  simp only [mem_image,mem_filter,Molecule.bonds,mem_univ,true_and]
  constructor
  · rintro ⟨y,ho,rfl⟩
    exact ⟨ho,y.property⟩
  · rintro ⟨ho,hx⟩
    exact ⟨⟨x,hx⟩,ho,rfl⟩

theorem bonds_card_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbSideMolecule M S hS).bonds.card = (M.bonds.filter (fun x => M.atom x ∈ S)).card := by
  rw [← bonds_closed_side_image M S hS,card_image_of_injective _ Subtype.val_injective]

theorem bonds_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    M.bonds.card = (appbSideMolecule M S hS).bonds.card+
      (appbSideMolecule M (M.atoms \ S) hS.complement).bonds.card := by
  classical
  rw [bonds_card_closed_side,bonds_card_closed_side]
  have he : M.bonds.filter (fun x => M.atom x ∈ M.atoms \ S) =
      M.bonds.filter (fun x => ¬M.atom x ∈ S) := by
    ext x
    simp only [mem_filter,mem_sdiff,M.atom_mem,true_and]
  rw [he,card_filter_add_card_filter_not]

theorem atoms_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    M.atoms.card = (appbSideMolecule M S hS).atoms.card+
      (appbSideMolecule M (M.atoms \ S) hS.complement).atoms.card := by
  change M.atoms.card = S.card+(M.atoms \ S).card
  have hh := card_sdiff_add_card_eq_card hS.subset_atoms
  omega

theorem circuitRank_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    M.circuitRank = (appbSideMolecule M S hS).circuitRank+
      (appbSideMolecule M (M.atoms \ S) hS.complement).circuitRank := by
  have ha := atoms_card_closed_side_add M S hS
  have hb := bonds_card_closed_side_add M S hS
  have hf := numComponents_closed_side_add M S hS
  unfold Molecule.circuitRank
  omega

end WaveTurbulence.Mole.AppbAlgorithm
