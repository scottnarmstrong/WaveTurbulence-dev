/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ScaleConditions
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Boundary
import Mathlib.Tactic

/-! # The sub-molecule induced on an atom set

`piece N Y` keeps the atoms of `Y` and every bond with both ends in `Y` (the erasure of the complement). The removed
part of a (Y) sequence is counted through it (DH23 L1952–L1956: "going from bottom to top" through the chain).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The sub-molecule induced on `Y`. -/
abbrev piece (N : Molecule V D) (Y : Finset V) := Degen.eraseAtoms N (N.atoms \ Y)

omit [Fintype D] [DecidableEq D] in
theorem piece_atoms {N : Molecule V D} {Y : Finset V} (hY : Y ⊆ N.atoms) : (piece N Y).atoms = Y := by
  change N.atoms \ (N.atoms \ Y) = Y
  rw [sdiff_sdiff_right_self, inf_eq_right.mpr hY]

omit [Fintype D] [DecidableEq D] in
/-- A dart of the piece has both ends in `Y`. -/
theorem piece_dart_mem {N : Molecule V D} {Y : Finset V} (x : Degen.RetainedDart N (N.atoms \ Y)) :
    N.atom x.val ∈ Y ∧ N.atom (N.mate x.val) ∈ Y := by
  obtain ⟨h1, h2⟩ := x.property
  simp only [mem_sdiff, not_and, not_not] at h1 h2
  exact ⟨h1 (N.atom_mem _), h2 (N.atom_mem _)⟩

/-- A dart with both ends in `Y`, as a dart of the piece. -/
def pieceDart (N : Molecule V D) (Y : Finset V) (x : D) (hx : N.atom x ∈ Y ∧ N.atom (N.mate x) ∈ Y) :
    Degen.RetainedDart N (N.atoms \ Y) :=
  ⟨x, fun h => (mem_sdiff.mp h).2 hx.1, fun h => (mem_sdiff.mp h).2 hx.2⟩

/-- Cells of the piece are the cells of `N` inside `Y`. -/
theorem isLadderCell_piece_iff {N : Molecule V D} {Y : Finset V} (S : Finset V) :
    MoleProp.IsLadderCell (piece N Y) S ↔ MoleProp.IsLadderCell N S ∧ S ⊆ Y := by
  rw [MoleProp.isLadderCell_erase_iff]
  refine and_congr_right fun hS => ?_
  have hSA := MoleProp.isLadderCell_subset_atoms N hS
  constructor
  · intro hd v hv
    by_contra hvY
    exact disjoint_left.mp hd hv (mem_sdiff.mpr ⟨hSA hv, hvY⟩)
  · intro hsub
    exact disjoint_left.mpr fun v hv hv' => (mem_sdiff.mp hv').2 (hsub hv)

omit [DecidableEq D] in
/-- The out- and in-degree caps pass to every erasure. -/
theorem caps_eraseAtoms {N : Molecule V D} (Z : Finset V)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) :
    ∀ v ∈ (Degen.eraseAtoms N Z).atoms, (Degen.eraseAtoms N Z).outdeg v ≤ 2 ∧
      (Degen.eraseAtoms N Z).indeg v ≤ 2 := by
  intro v hv
  have hv' := (mem_sdiff.mp hv).1
  have hle : ∀ b : Bool, ((Degen.eraseAtoms N Z).dartsAt v |>.filter fun x => N.out x.val = b).card ≤
      ((N.dartsAt v).filter fun x => N.out x = b).card := by
    intro b
    refine card_le_card_of_injOn (fun x => x.val) ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, Molecule.dartsAt, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx
    · intro x _ y _ h
      exact Subtype.ext h
  refine ⟨(hle true).trans (hcap v hv').1, (hle false).trans (hcap v hv').2⟩

/-- The degree of a surviving atom splits into retained and removed darts. -/
theorem deg_eraseAtoms_add {N : Molecule V D} (Z : Finset V) {v : V} (hv : v ∉ Z) :
    (Degen.eraseAtoms N Z).deg v + (Degen.removedDartsAt N Z v).card = N.deg v := by
  have h := Degen.sum_dartsAt_split N Z hv (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one] at h
  unfold Molecule.deg
  omega

omit [DecidableEq D] in
/-- `piece N Y` is a molecule (DH23 L633) when its connected and some atom of it has degree `≠ 4`. -/
theorem piece_isMolecule {N : Molecule V D} {Y : Finset V} (hY : Y ⊆ N.atoms)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hconn : ∀ u ∈ Y, ∀ v ∈ Y, (piece N Y).SameComponent u v)
    {z : V} (hz : z ∈ Y) (hz4 : (piece N Y).deg z ≠ 4) : (piece N Y).IsMolecule := by
  refine ⟨caps_eraseAtoms _ hcap, fun v hv => ⟨z, ?_, ?_, hz4⟩⟩
  · rw [piece_atoms hY]; exact hz
  · rw [piece_atoms hY] at hv; exact hconn v hv z hz

end WaveTurbulence.MoleProp4
