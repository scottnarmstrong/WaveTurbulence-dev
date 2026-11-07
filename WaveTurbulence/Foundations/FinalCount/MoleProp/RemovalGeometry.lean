/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.DegreeTwoReduction
public import WaveTurbulence.Foundations.FinalCount.Degen.EraseMolecule
import Mathlib.Tactic

/-! # DH23 Proposition 10.1: actual operation-priority geometry

Nonsaturation produces a removable atom. If that atom belongs to a
positive-length selected ladder, its actual rung gives operation (b),
which takes priority. Otherwise deleting it preserves the ladder family.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 proof of Proposition 10.1, L1843: every nonempty molecule has
an atom of degree at most three, without a connectivity assumption. -/
theorem exists_atom_degree_le_three (M : Molecule V D) (hM : M.IsMolecule)
    (hne : M.atoms.Nonempty) : ∃ z ∈ M.atoms, M.deg z ≤ 3 := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨z,hz,_haz,hz4⟩ := hM.2 a ha
  have hc := Mole.deg_le_four M hM hz
  exact ⟨z,hz,by omega⟩

/-- An actual low-degree atom on a selected rung already supplies the
pair required by operation (b): degrees three and three or four. -/
theorem sourceLadder_row_operation_b_pair (M : Molecule V D) (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (hL : SourceLadder M u v)
    (j : Fin (m+1)) (hsmall : M.deg (u j) ≤ 3) :
    ∃ b ∈ M.atoms, u j ≠ b ∧ M.deg (u j) = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween (u j) b = 2 := by
  have hu3 := sourceLadder_row_degree_ge_three M hL j
  have hv3 := sourceLadder_row_degree_ge_three M (sourceLadder_swap M hL) j
  have hv4 := Mole.deg_le_four M hM (hL.2.2.1 j).2
  have huv : u j ≠ v j := by
    intro he
    have hh : (Sum.inl j : Fin (m+1) ⊕ Fin (m+1)) = Sum.inr j := hL.2.1 he
    cases hh
  exact ⟨v j,(hL.2.2.1 j).2,huv,by omega,by omega,hL.2.2.2.1 j⟩

/-- DH23 L1845: any degree-at-most-three atom in a genuine ladder has
an actual double-bond neighbor making operation (b) available. -/
theorem operation_b_pair_of_sourceLadder_mem (M : Molecule V D) (hM : M.IsMolecule)
    {z : V} (hsmall : M.deg z ≤ 3) {S : Finset V} (hS : SourceLadderSet M S)
    (hz : z ∈ S) :
    ∃ b ∈ M.atoms, z ≠ b ∧ M.deg z = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween z b = 2 := by
  obtain ⟨m,u,v,hL,rfl⟩ := hS
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_row_operation_b_pair M hM hL j hsmall
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_row_operation_b_pair M hM (sourceLadder_swap M hL) j hsmall

/-- Priority of operation (b) excludes the selected atom from every actual
positive-length source ladder; no reduction-state premise is used. -/
theorem not_mem_sourceLadder_of_no_operation_b (M : Molecule V D) (hM : M.IsMolecule)
    {z : V} (hz : z ∈ M.atoms) (hsmall : M.deg z ≤ 3)
    (hno : ¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2)
    (S : Finset V) (hS : SourceLadderSet M S) : z ∉ S := by
  intro hzS
  obtain ⟨b,hb,hab,ha3,hb34,hd⟩ := operation_b_pair_of_sourceLadder_mem M hM hsmall hS hzS
  exact hno ⟨z,hz,b,hb,hab,ha3,hb34,hd⟩

/-- Operation (a), performed only when (b) is unavailable, leaves the
literal maximal selected-ladder family unchanged. -/
theorem sourceMaximalLadders_erase_eq_of_no_operation_b (M : Molecule V D) (hM : M.IsMolecule)
    {z : V} (hz : z ∈ M.atoms) (hsmall : M.deg z ≤ 3)
    (hno : ¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) :
    sourceMaximalLadders (eraseAtoms M {z}) = sourceMaximalLadders M := by
  apply sourceMaximalLadders_erase_eq_of_all_disjoint M {z}
  intro S hS
  exact disjoint_singleton_right.mpr (not_mem_sourceLadder_of_no_operation_b M hM hz hsmall hno S hS)

/-- The finite algorithm always has an actual priority-respecting next
removal: either an operation-(b) pair, or a low-degree atom whose deletion
preserves the molecule axioms and its maximal selected-ladder family. -/
theorem exists_priority_removal (M : Molecule V D) (hM : M.IsMolecule)
    (hne : M.atoms.Nonempty) :
    (∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2) ∨
    ∃ z ∈ M.atoms, M.deg z ≤ 3 ∧ (eraseAtoms M {z}).IsMolecule ∧
      sourceMaximalLadders (eraseAtoms M {z}) = sourceMaximalLadders M := by
  classical
  by_cases hb : ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2
  · exact Or.inl hb
  · obtain ⟨z,hz,hsmall⟩ := exists_atom_degree_le_three M hM hne
    exact Or.inr ⟨z,hz,hsmall,isMolecule_eraseAtoms M hM {z},
      sourceMaximalLadders_erase_eq_of_no_operation_b M hM hz hsmall hb⟩

end WaveTurbulence.MoleProp
