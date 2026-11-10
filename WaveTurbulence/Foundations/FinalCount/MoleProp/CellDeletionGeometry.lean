/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.MoleProp.RemovalGeometry
import Mathlib.Tactic

/-! # Operation (b) deletes at most one actual ladder cell -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem exists_cell_start_at (M : Molecule V D) {S : Finset V}
    (hS : IsLadderCell M S) {a : V} (ha : a ∈ S) :
    ∃ u v : Fin 2 → V, SourceLadder M u v ∧ Molecule.ladderAtoms u v = S ∧ u 0 = a := by
  obtain ⟨u,v,hL,rfl⟩ := hS
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨u,v,hL,rfl,rfl⟩
    · exact ⟨fun i => u i.rev,fun i => v i.rev,sourceLadder_reverse M hL,
        ladderAtoms_reverse u v,rfl⟩
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    fin_cases j
    · exact ⟨v,u,sourceLadder_swap M hL,ladderAtoms_swap u v,rfl⟩
    · refine ⟨fun i => v i.rev,fun i => u i.rev,sourceLadder_reverse M (sourceLadder_swap M hL),?_,rfl⟩
      rw [ladderAtoms_reverse,ladderAtoms_swap]

/-- A degree-three atom lies in at most one actual selected ladder cell.
Its double rung, single rail, and opposite rung partner are all forced. -/
theorem isLadderCell_eq_of_degree_three_mem (M : Molecule V D) (hM : M.IsMolecule)
    {a : V} (hdeg : M.deg a = 3) {S T : Finset V}
    (hS : IsLadderCell M S) (hT : IsLadderCell M T) (haS : a ∈ S) (haT : a ∈ T) : S = T := by
  obtain ⟨u,v,hL,hUS,hu0⟩ := exists_cell_start_at M hS haS
  obtain ⟨p,q,hK,hPT,hp0⟩ := exists_cell_start_at M hT haT
  have hcap : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hM hx
  obtain ⟨hu,hv,huv⟩ := Sum.elim_injective.mp hL.2.1
  obtain ⟨hp,hq,hpq⟩ := Sum.elim_injective.mp hK.2.1
  have hzero : p 0 = u 0 := hp0.trans hu0.symm
  have hqzero : q 0 = v 0 := by
    apply sourceLadder_double_partner_eq M hcap hL 0
    · rw [← hzero]; exact hpq 0 0
    · rw [← hzero]; exact hK.2.2.2.1 0
  have hrail : M.bondsBetween (u 0) (u 1) = 1 := (hL.2.2.2.2 0).1
  have hprail : M.bondsBetween (u 0) (p 1) = 1 := by
    rw [← hzero]; exact (hK.2.2.2.2 0).1
  have hpone : p 1 = u 1 := by
    by_contra hne
    have hh := three_neighbor_bonds_le_degree M (huv 0 0)
      (hu.ne (by decide : (0 : Fin 2) ≠ 1))
      (by rw [← hzero]; exact hp.ne (by decide : (0 : Fin 2) ≠ 1))
      (huv 1 0).symm (by rw [← hqzero]; exact (hpq 1 0).symm) (fun hh => hne hh.symm)
    rw [hL.2.2.2.1 0,hrail,hprail,hu0,hdeg] at hh
    omega
  have hqone : q 1 = v 1 := by
    apply sourceLadder_double_partner_eq M hcap hL 1
    · rw [← hpone]; exact hpq 1 1
    · rw [← hpone]; exact hK.2.2.2.1 1
  have hpu : p = u := by funext i; fin_cases i; exact hzero; exact hpone
  have hqv : q = v := by funext i; fin_cases i; exact hqzero; exact hqone
  subst p
  subst q
  exact hUS.symm.trans hPT

/-- Every cell meeting an operation-(b) double-rung pair contains its
degree-three endpoint; the partner is forced by double-rung uniqueness. -/
theorem cell_disjoint_double_pair_iff (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2)
    {S : Finset V} (hS : IsLadderCell M S) : Disjoint S {a,b} ↔ a ∉ S := by
  constructor
  · intro hd ha
    exact disjoint_left.mp hd ha (by simp)
  · intro ha
    apply disjoint_left.mpr
    intro x hx hpair
    rcases mem_insert.mp hpair with rfl | hx'
    · exact ha hx
    · have hxb : x = b := mem_singleton.mp hx'
      subst x
      obtain ⟨u,v,hL,hLS⟩ := hS
      have hb : b ∈ Molecule.ladderAtoms u v := hLS.symm ▸ hx
      have ha' := sourceLadder_partner_mem M (fun x hx => Mole.deg_le_four M hM hx)
        hL hb hab.symm (by rw [bondsBetween_comm]; exact hdouble)
      exact ha (hLS ▸ ha')

/-- DH23 operation (b) affects at most one actual per-position ladder factor. -/
theorem card_cells_lost_double_pair_le_one (M : Molecule V D) (hM : M.IsMolecule)
    {a b : V} (hab : a ≠ b) (hdeg : M.deg a = 3) (hdouble : M.bondsBetween a b = 2) :
    ((ladderCells M).filter (fun S => ¬ Disjoint S {a,b})).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro S hS T hT
  obtain ⟨hS,hSa⟩ := mem_filter.mp hS
  obtain ⟨hT,hTa⟩ := mem_filter.mp hT
  have hSC : IsLadderCell M S := (mem_filter.mp hS).2
  have hTC : IsLadderCell M T := (mem_filter.mp hT).2
  have haS : a ∈ S := by
    by_contra ha
    exact hSa ((cell_disjoint_double_pair_iff M hM hab hdouble hSC).mpr ha)
  have haT : a ∈ T := by
    by_contra ha
    exact hTa ((cell_disjoint_double_pair_iff M hM hab hdouble hTC).mpr ha)
  exact isLadderCell_eq_of_degree_three_mem M hM hdeg hSC hTC haS haT

/-- The actual per-position cell family is unchanged in priority operation (a). -/
theorem ladderCells_erase_eq_of_no_operation_b (M : Molecule V D) (hM : M.IsMolecule)
    {z : V} (hz : z ∈ M.atoms) (hsmall : M.deg z ≤ 3)
    (hno : ¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) :
    ladderCells (eraseAtoms M {z}) = ladderCells M := by
  classical
  rw [ladderCells_erase_eq_filter]
  apply filter_eq_self.mpr
  intro S hS
  obtain ⟨u,v,hL,hLS⟩ := (mem_filter.mp hS).2
  exact disjoint_singleton_right.mpr
    (not_mem_sourceLadder_of_no_operation_b M hM hz hsmall hno S ⟨1,u,v,hL,hLS⟩)

end WaveTurbulence.MoleProp
