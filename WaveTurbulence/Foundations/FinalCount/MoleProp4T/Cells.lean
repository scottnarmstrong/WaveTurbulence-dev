/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LadderCells
public import WaveTurbulence.Foundations.FinalCount.WorldSelectedLadderDisjoint
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Ladder cells near a modified spot

The per-position ladder factors of DH23 L1831 (`MoleProp.cellProduct`) are attached to the cells: two double rungs
and their two opposite rails. An operation that changes the molecule only near one atom changes only the cells
containing that atom, and an atom of degree at most four lies in at most two cells. So a (Y) sequence changes only
`O(1)` ladder factors, as DH23 L1952 uses ("for all but `O(1)` operations ... `𝔇 ≲ 1`").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Without loops there is no bond from an atom to itself. -/
theorem bondsBetween_self_eq_zero {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) (c : V) :
    M.bondsBetween c c = 0 := by
  unfold Molecule.bondsBetween
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have h := Sym2.eq_iff.mp hx
  simp only [or_self] at h
  exact hloop x (h.1.trans h.2.symm)

omit [DecidableEq D] in
/-- A degree-four atom with a double partner `p` and a single neighbour `q` has no other double partner. -/
theorem double_partner_unique {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {c p q : V}
    (hdeg : M.deg c ≤ 4) (hp : M.bondsBetween c p = 2) (hq : M.bondsBetween c q = 1) {p' : V}
    (hp' : M.bondsBetween c p' = 2) : p' = p := by
  by_contra hne
  have hcp : c ≠ p := by intro h; rw [← h, bondsBetween_self_eq_zero hloop] at hp; omega
  have hcq : c ≠ q := by intro h; rw [← h, bondsBetween_self_eq_zero hloop] at hq; omega
  have hcp' : c ≠ p' := by intro h; rw [← h, bondsBetween_self_eq_zero hloop] at hp'; omega
  have hpq : p ≠ q := by intro h; rw [h] at hp; omega
  have hp'q : p' ≠ q := by intro h; rw [h] at hp'; omega
  have h := Degen.sum_neighbor_bonds_le_degree M c {p, q, p'} (by simp [hcp, hcq, hcp'])
  rw [sum_insert (by simp [hpq, Ne.symm hne]), sum_insert (by simp [hp'q.symm]), sum_singleton, hp, hq, hp'] at h
  omega

omit [DecidableEq D] in
/-- Every atom of a cell has a double partner `p`, a single neighbour `q` whose double partner is `q'`, and the cell
is `{c, p, q, q'}`. -/
theorem cell_quad {M : Molecule V D} {u v : Fin 2 → V} (h : Degen.SourceLadder M u v) {c : V}
    (hc : c ∈ Molecule.ladderAtoms u v) :
    ∃ p q q', M.bondsBetween c p = 2 ∧ M.bondsBetween c q = 1 ∧ M.bondsBetween q q' = 2 ∧
      Molecule.ladderAtoms u v = {c, p, q, q'} := by
  obtain ⟨_, _, _, hrung, hrail⟩ := h
  obtain ⟨hu, hv, _⟩ := hrail 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at hu hv
  have hS : Molecule.ladderAtoms u v = {u 0, u 1, v 0, v 1} := by
    ext z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩]
  rw [hS] at hc ⊢
  have r0 := hrung 0
  have r1 := hrung 1
  have r0' : M.bondsBetween (v 0) (u 0) = 2 := by rw [Degen.bondsBetween_comm]; exact r0
  have r1' : M.bondsBetween (v 1) (u 1) = 2 := by rw [Degen.bondsBetween_comm]; exact r1
  have hu' : M.bondsBetween (u 1) (u 0) = 1 := by rw [Degen.bondsBetween_comm]; exact hu
  have hv' : M.bondsBetween (v 1) (v 0) = 1 := by rw [Degen.bondsBetween_comm]; exact hv
  simp only [mem_insert, mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨v 0, u 1, v 1, r0, hu, r1, by ext; simp only [mem_insert, mem_singleton]; tauto⟩
  · exact ⟨v 1, u 0, v 0, r1, hu', r0, by ext; simp only [mem_insert, mem_singleton]; tauto⟩
  · exact ⟨u 0, v 1, u 1, r0', hv, r1', by ext; simp only [mem_insert, mem_singleton]; tauto⟩
  · exact ⟨u 1, v 0, u 0, r1', hv', r0', by ext; simp only [mem_insert, mem_singleton]; tauto⟩

/-- The single neighbours of `c`. -/
noncomputable def singleNbrs (M : Molecule V D) (c : V) : Finset V := by
  classical
  exact M.atoms.filter fun q => M.bondsBetween c q = 1

/-- The double partners of `c`. -/
noncomputable def doubleNbrs (M : Molecule V D) (c : V) : Finset V := by
  classical
  exact M.atoms.filter fun q => M.bondsBetween c q = 2

omit [DecidableEq D] in
theorem mem_atoms_of_bondsBetween_pos {M : Molecule V D} {a b : V} (h : 0 < M.bondsBetween a b) :
    b ∈ M.atoms := by
  obtain ⟨x, hx⟩ := card_pos.mp h
  have hx' := (mem_filter.mp hx).2
  have he := Sym2.eq_iff.mp hx'
  rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
  · rw [← h2]; exact M.atom_mem _
  · rw [← h1]; exact M.atom_mem _

/-- The cell through `c` with single neighbour `q`, as a function of `q`. -/
noncomputable def cellThrough (M : Molecule V D) (c q : V) : Finset V :=
  {c, q} ∪ doubleNbrs M c ∪ doubleNbrs M q

/-- **At most two cells contain a given atom** (degree caps `≤ 4`, no loops). -/
theorem card_cells_containing_le_two {M : Molecule V D} (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4) (c : V) :
    ((MoleProp.ladderCells M).filter fun S => c ∈ S).card ≤ 2 := by
  classical
  have hsub : (MoleProp.ladderCells M).filter (fun S => c ∈ S) ⊆ (singleNbrs M c).image (cellThrough M c) := by
    intro S hS
    obtain ⟨hS, hcS⟩ := mem_filter.mp hS
    obtain ⟨_, u, v, hL, rfl⟩ := mem_filter.mp hS
    obtain ⟨p, q, q', hp, hq, hq', hset⟩ := cell_quad hL hcS
    have hc : c ∈ M.atoms := MoleProp.isLadderCell_subset_atoms M ⟨u, v, hL, rfl⟩ hcS
    have hqA : q ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := c) (by omega)
    refine mem_image.mpr ⟨q, mem_filter.mpr ⟨hqA, hq⟩, ?_⟩
    have hdc : doubleNbrs M c = {p} := by
      ext z
      simp only [doubleNbrs, mem_filter, mem_singleton]
      constructor
      · rintro ⟨_, hz⟩; exact double_partner_unique hloop (hdeg c hc) hp hq hz
      · rintro rfl; exact ⟨mem_atoms_of_bondsBetween_pos (a := c) (by omega), hp⟩
    have hqc : M.bondsBetween q c = 1 := by rw [Degen.bondsBetween_comm]; exact hq
    have hdq : doubleNbrs M q = {q'} := by
      ext z
      simp only [doubleNbrs, mem_filter, mem_singleton]
      constructor
      · rintro ⟨_, hz⟩; exact double_partner_unique hloop (hdeg q hqA) hq' hqc hz
      · rintro rfl; exact ⟨mem_atoms_of_bondsBetween_pos (a := q) (by omega), hq'⟩
    rw [hset, cellThrough, hdc, hdq]
    ext z; simp only [mem_union, mem_insert, mem_singleton]; tauto
  by_cases hcS : ∃ p, M.bondsBetween c p = 2
  · refine (card_le_card hsub).trans (card_image_le.trans ?_)
    obtain ⟨p, hp⟩ := hcS
    have hcp : c ≠ p := by intro h; rw [← h, bondsBetween_self_eq_zero hloop] at hp; omega
    have hpn : p ∉ singleNbrs M c := by simp [singleNbrs, hp]
    have hcn : c ∉ insert p (singleNbrs M c) := by
      simp only [mem_insert, singleNbrs, mem_filter, bondsBetween_self_eq_zero hloop, not_or]
      exact ⟨hcp, by omega⟩
    have h := Degen.sum_neighbor_bonds_le_degree M c (insert p (singleNbrs M c)) hcn
    rw [sum_insert hpn, hp] at h
    have hs : ∑ b ∈ singleNbrs M c, M.bondsBetween c b = (singleNbrs M c).card := by
      rw [card_eq_sum_ones]; exact sum_congr rfl fun b hb => (mem_filter.mp hb).2
    by_cases hc : c ∈ M.atoms
    · have := hdeg c hc; omega
    · have hd0 : M.deg c = 0 := by
        apply card_eq_zero.mpr; apply filter_eq_empty_iff.mpr
        intro x _ hx; exact hc (hx ▸ M.atom_mem x)
      omega
  · -- without a double partner, `c` lies in no cell
    push Not at hcS
    have hempty : (MoleProp.ladderCells M).filter (fun S => c ∈ S) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro S hS hcS'
      obtain ⟨_, u, v, hL, rfl⟩ := mem_filter.mp hS
      obtain ⟨p, _, _, hp, _⟩ := cell_quad hL hcS'
      exact hcS p hp
    rw [hempty, card_empty]; omega

end WaveTurbulence.MoleProp4
