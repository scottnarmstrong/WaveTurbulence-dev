/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalize
public import WaveTurbulence.Foundations.Molecule.EndRungLowerDarts
public import WaveTurbulence.Foundations.Molecule.EndRungBondCounts
public import WaveTurbulence.Foundations.Molecule.TypeIIEndRung
public import WaveTurbulence.Foundations.Molecule.TypeIILowerParent

/-! # Normalizing a type-II chart so that rung `0` is the end rung next to `b` (R20 (1))

The only inputs are the contract's `rung_bonds`, a degree-four count (`Molecpl.EndRungData`, whose `left_row` row
is a `FourIncidences`), and `Molecpl.garden_typeII_end_rung`.  `normalizeChart C` swaps rung `0` with an adjacent
rung when one exists; for a type-II vine of a garden one always exists (`exists_adjacent_rung`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract Finset Molecpl

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

/-- Every internal neighbour of the lower joint is one of the two rung atoms of an end rung. -/
theorem _root_.WaveTurbulence.Molecpl.EndRungData.eq_of_lower_bond (hB : M.IsBlock S a b) (R : EndRungData M S a b) {w : V} (hw : w ∈ S)
    (hwb : w ≠ b) (h : M.bondsBetween b w ≠ 0) : w = R.left ∨ w = R.right := by
  rw [bondsBetween_eq_internal_card hB.2.2.1 hw hwb.symm, R.lower_darts hB] at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [mem_filter, mem_insert, mem_singleton] at hx
  have hl : M.atom (M.mate (M.mate (R.left_row.dart 2))) = R.left := by
    rw [M.mate_mate]; exact R.left_row.atom_eq 2
  have hr : M.atom (M.mate (M.mate (R.right_row.dart 2))) = R.right := by
    rw [M.mate_mate]; exact R.right_row.atom_eq 2
  rcases hx with ⟨rfl | rfl, hxw⟩
  · left; rw [← hxw, hl]
  · right; rw [← hxw, hr]

/-- A rung partner of the left rung atom (a doubled neighbour other than `b`) is the right rung atom. -/
theorem _root_.WaveTurbulence.Molecpl.EndRungData.rung_partner (hM : M.IsMolecule) (R : EndRungData M S a b) {y : V} (hy : y ≠ b)
    (hyl : y ≠ R.left) (h2 : M.bondsBetween R.left y = 2) : y = R.right := by
  by_contra hyr
  rw [Mole.bondsBetween_eq_card_darts M hyl.symm, ← Vine.fourIncidences_image M hM R.left_row,
    Finset.filter_image, Finset.card_image_of_injective _ R.left_row.injective] at h2
  have hsub : (Finset.univ.filter (fun i : Fin 4 => M.atom (M.mate (R.left_row.dart i)) = y)) ⊆ {3} := by
    intro i hi
    rw [mem_filter, R.left_row.neighbor_eq i] at hi
    fin_cases i <;> simp_all
  have := Finset.card_le_card hsub
  simp at this
  omega

section Chart
variable {X : VineType}

theorem slot_cases (A : Shape X) (hX : X.IsBad = true) (i : Fin A.n) :
    i = A.x0 ∨ (∃ j, i = A.xSlot j) ∨ ∃ j, i = A.ySlot j := by
  have hi : i.1 < 2 * A.m + 1 := by
    have := i.2
    unfold Shape.n at this
    simpa [hX] using this
  by_cases h0 : i.1 = 0
  · left; ext; simp [Shape.x0, h0]
  by_cases h1 : i.1 ≤ A.m
  · right; left
    refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩
    ext; simp [Shape.xSlot]; omega
  · right; right
    refine ⟨⟨i.1 - (A.m + 1), by omega⟩, ?_⟩
    ext; simp [Shape.ySlot]; omega

theorem xSlot_ne_ySlot (A : Shape X) (j k : Fin A.m) : A.xSlot j ≠ A.ySlot k := by
  intro h
  have := congrArg Fin.val h
  simp [Shape.xSlot, Shape.ySlot] at this
  have := k.2
  have := j.2
  omega

theorem xSlot_ne_x0 (A : Shape X) (j : Fin A.m) : A.xSlot j ≠ A.x0 := by
  intro h
  have := congrArg Fin.val h
  simp [Shape.xSlot, Shape.x0] at this

theorem ySlot_ne_x0 (A : Shape X) (j : Fin A.m) : A.ySlot j ≠ A.x0 := by
  intro h
  have := congrArg Fin.val h
  simp [Shape.ySlot, Shape.x0] at this

theorem atom_ne_lower (C : FullVineChart M X S a b) {i : Fin C.indexing.shape.n}
    (hi : i ≠ C.indexing.shape.x0) : (C.indexing.atom i).1 ≠ b := by
  intro h
  apply hi
  apply C.indexing.atom.injective
  apply Subtype.ext
  rw [h]; exact C.indexing.lower.symm

theorem atom_mem (C : FullVineChart M X S a b) (i : Fin C.indexing.shape.n) : (C.indexing.atom i).1 ∈ S :=
  (Finset.mem_erase.mp (C.indexing.atom i).2).2

theorem atom_ne_upper (C : FullVineChart M X S a b) (i : Fin C.indexing.shape.n) : (C.indexing.atom i).1 ≠ a :=
  (Finset.mem_erase.mp (C.indexing.atom i).2).1

theorem junction_none (C : FullVineChart M .II S a b) : C.junction = none := by
  have h := C.junction_type
  revert h
  cases C.junction <;> simp <;> decide

theorem rung_bonds_two (C : FullVineChart M .II S a b) (j : Fin C.indexing.shape.m) :
    M.bondsBetween (C.indexing.atom (C.indexing.shape.xSlot j)).1
      (C.indexing.atom (C.indexing.shape.ySlot j)).1 = 2 := by
  have h := C.rung_bonds j
  rw [junction_none C] at h
  simpa using h

/-- Every interior atom of a type-II vine is a rung atom of the chart. -/
theorem rung_of_atom (C : FullVineChart M .II S a b) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ j, (C.indexing.atom (C.indexing.shape.xSlot j)).1 = v ∨
      (C.indexing.atom (C.indexing.shape.ySlot j)).1 = v := by
  let i := C.indexing.atom.symm ⟨v, Finset.mem_erase.mpr ⟨hva, hv⟩⟩
  have hi : (C.indexing.atom i).1 = v := by simp [i]
  rcases slot_cases C.indexing.shape rfl i with h | ⟨j, h⟩ | ⟨j, h⟩
  · exact absurd (by rw [← hi, h]; exact C.indexing.lower) hvb
  · exact ⟨j, Or.inl (by rw [← hi, h])⟩
  · exact ⟨j, Or.inr (by rw [← hi, h])⟩

/-- **Existence of an adjacent rung** for a type-II vine with end-rung data. -/
theorem exists_adjacent_rung (hM : M.IsMolecule) (hB : M.IsBlock S a b) (R : EndRungData M S a b)
    (C : FullVineChart M .II S a b) : ∃ j, Adj C j := by
  obtain ⟨j, hj⟩ := rung_of_atom C R.left_mem R.left_ne_upper R.left_ne_lower
  have hx := atom_ne_lower C (xSlot_ne_x0 C.indexing.shape j)
  have hy := atom_ne_lower C (ySlot_ne_x0 C.indexing.shape j)
  have h2 := rung_bonds_two C j
  have hs := R.lower_single_counts hB
  refine ⟨j, ?_⟩
  unfold Adj
  rcases hj with hj | hj
  · have hr : (C.indexing.atom (C.indexing.shape.ySlot j)).1 = R.right := by
      refine R.rung_partner hM hy ?_ (by rw [hj] at h2; exact h2)
      rw [← hj]
      intro h
      exact xSlot_ne_ySlot _ j j (C.indexing.atom.injective (Subtype.ext h.symm))
    rw [hr, hj]
    exact ⟨by rw [hs.1]; norm_num, by rw [hs.2]; norm_num⟩
  · have hr : (C.indexing.atom (C.indexing.shape.xSlot j)).1 = R.right := by
      refine R.rung_partner hM hx ?_ (by rw [hj, Mole.bondsBetween_symm] at h2; exact h2)
      rw [← hj]
      intro h
      exact xSlot_ne_ySlot _ j j (C.indexing.atom.injective (Subtype.ext h))
    rw [hr, hj]
    exact ⟨by rw [hs.2]; norm_num, by rw [hs.1]; norm_num⟩

/-- An adjacent rung consists of the two end-rung atoms. -/
theorem adj_pair (hB : M.IsBlock S a b) (R : EndRungData M S a b) (C : FullVineChart M X S a b)
    (j : Fin C.indexing.shape.m) (hj : Adj C j) (hxb : C.indexing.shape.xSlot j ≠ C.indexing.shape.x0)
    (hyb : C.indexing.shape.ySlot j ≠ C.indexing.shape.x0) :
    ((C.indexing.atom (C.indexing.shape.xSlot j)).1 = R.left ∧
        (C.indexing.atom (C.indexing.shape.ySlot j)).1 = R.right) ∨
      ((C.indexing.atom (C.indexing.shape.xSlot j)).1 = R.right ∧
        (C.indexing.atom (C.indexing.shape.ySlot j)).1 = R.left) := by
  have hx := R.eq_of_lower_bond hB (atom_mem C _) (atom_ne_lower C hxb) hj.1
  have hy := R.eq_of_lower_bond hB (atom_mem C _) (atom_ne_lower C hyb) hj.2
  have hne : (C.indexing.atom (C.indexing.shape.xSlot j)).1 ≠ (C.indexing.atom (C.indexing.shape.ySlot j)).1 := by
    intro h
    exact xSlot_ne_ySlot _ j j (C.indexing.atom.injective (Subtype.ext h))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hne
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hx.trans hy.symm) hne

end Chart

end WaveTurbulence.VineEstS3
