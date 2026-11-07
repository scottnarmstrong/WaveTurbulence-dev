/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideMolecule
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideCircuitRank
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideLinkProduct
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActivePotential
import Mathlib.Tactic

/-! # Additivity of the source graph statistics over closed sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem filter_card_closed_partition (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (Q : V → Prop) [DecidablePred Q] :
    (M.atoms.filter Q).card = (S.filter Q).card+((M.atoms \ S).filter Q).card := by
  classical
  have hd : Disjoint (S.filter Q) ((M.atoms \ S).filter Q) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp (mem_filter.mp hb).1).2 (mem_filter.mp ha).1
  have he : M.atoms.filter Q = S.filter Q ∪ (M.atoms \ S).filter Q := by
    rw [← filter_union,union_sdiff_of_subset hS.subset_atoms]
  rw [he,card_union_of_disjoint hd]

theorem degreeAtoms_closed_side_filter (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (j : ℕ) : appbDegreeAtoms (appbSideMolecule M S hS) j = S.filter (fun a => M.deg a = j) := by
  classical
  ext a
  simp only [appbDegreeAtoms,mem_filter]
  constructor
  · rintro ⟨ha,hd⟩
    exact ⟨ha,(degree_closed_side M S hS ha).symm.trans hd⟩
  · rintro ⟨ha,hd⟩
    exact ⟨ha,(degree_closed_side M S hS ha).trans hd⟩

theorem degreeAtoms_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (j : ℕ) : (appbDegreeAtoms M j).card = (appbDegreeAtoms (appbSideMolecule M S hS) j).card+
      (appbDegreeAtoms (appbSideMolecule M (M.atoms \ S) hS.complement) j).card := by
  classical
  rw [degreeAtoms_closed_side_filter,degreeAtoms_closed_side_filter]
  exact filter_card_closed_partition M S hS (fun a => M.deg a = j)

theorem nu_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    appbNu M = appbNu (appbSideMolecule M S hS)+
      appbNu (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  have ha := atoms_card_closed_side_add M S hS
  have hb := bonds_card_closed_side_add M S hS
  have hf := numComponents_closed_side_add M S hS
  unfold appbNu
  omega

theorem links_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbLinks M).card = (appbLinks (appbSideMolecule M S hS)).card+
      (appbLinks (appbSideMolecule M (M.atoms \ S) hS.complement)).card := by
  rw [links_closed_side_union M S hS,card_union_of_disjoint (links_closed_side_disjoint M S hS)]

theorem linkPotential_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    linkPotential M = linkPotential (appbSideMolecule M S hS)+
      linkPotential (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  have ha := atoms_card_closed_side_add M S hS
  have hl := links_card_closed_side_add M S hS
  unfold linkPotential
  omega

theorem activeLinkPotential_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    activeLinkPotential M = activeLinkPotential (appbSideMolecule M S hS)+
      activeLinkPotential (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  have hk := linkPotential_closed_side_add M S hS
  have h0 := degreeAtoms_card_closed_side_add M S hS 0
  unfold activeLinkPotential
  omega

end WaveTurbulence.Mole.AppbAlgorithm
