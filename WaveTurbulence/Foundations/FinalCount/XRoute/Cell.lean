/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Basic
import Mathlib.Tactic

/-! # G8-XROUTE (a), (b): the only small cell is `X`

A loop-free 4-regular molecule with at most four atoms that has a ladder cell is `X`
(case-4 research note, Fact 1.1).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The degree of an atom of a four-atom molecule as a sum of three bond counts. -/
theorem deg_eq_three {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : M.atoms = {a, b, c, d}) :
    M.deg a = M.bondsBetween a b + M.bondsBetween a c + M.bondsBetween a d := by
  rw [deg_eq_sum_bb M hloop a, hs]
  have : ({a, b, c, d} : Finset V).erase a = {b, c, d} := by
    ext z; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2 | h2⟩
      · exact absurd h2 h1
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨hab.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨hac.symm, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨had.symm, Or.inr (Or.inr (Or.inr rfl))⟩
  rw [this, sum_insert (by simp [hbc, hbd]), sum_pair hcd]
  ring

/-- **(b) `isX_of_smallCell`**: a 4-regular loop-free molecule with at most four atoms and a ladder cell is `X`. -/
theorem isX_of_smallCell {M : Molecule V D} (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z))
    (hreg : ∀ a ∈ M.atoms, M.deg a = 4) (hcard : M.atoms.card ≤ 4)
    (hcell : (MoleProp.ladderCells M).Nonempty) : IsX M := by
  classical
  obtain ⟨S, hS⟩ := hcell
  obtain ⟨hsub, u, w, hL, rfl⟩ := mem_filter.mp hS
  obtain ⟨_, hinj, hat, hrung, hrail⟩ := hL
  have hsub' := mem_powerset.mp hsub
  have hset : Molecule.ladderAtoms u w = {u 0, w 0, u 1, w 1} := by
    ext z
    simp only [Molecule.ladderAtoms, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩) <;> fin_cases a <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl ⟨0, rfl⟩, Or.inr ⟨0, rfl⟩, Or.inl ⟨1, rfl⟩, Or.inr ⟨1, rfl⟩]
  have hne : ∀ i j : Fin 2, i ≠ j → u i ≠ u j := fun i j h e =>
    h (Sum.inl_injective (hinj (show Sum.elim u w (Sum.inl i) = Sum.elim u w (Sum.inl j) from e)))
  have hne' : ∀ i j : Fin 2, i ≠ j → w i ≠ w j := fun i j h e =>
    h (Sum.inr_injective (hinj (show Sum.elim u w (Sum.inr i) = Sum.elim u w (Sum.inr j) from e)))
  have hne'' : ∀ i j : Fin 2, u i ≠ w j := fun i j e =>
    Sum.inl_ne_inr (hinj (show Sum.elim u w (Sum.inl i) = Sum.elim u w (Sum.inr j) from e))
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hc4 : (Molecule.ladderAtoms u w).card = 4 := by
    rw [Degen.ladderAtoms_card_of_injective hinj]
  have hs : M.atoms = {u 0, w 0, u 1, w 1} := by
    rw [← hset]
    exact (eq_of_subset_of_card_le hsub' (hcard.trans hc4.ge)).symm
  have r0 : M.bondsBetween (u 0) (w 0) = 2 := hrung 0
  have r1 : M.bondsBetween (u 1) (w 1) = 2 := hrung 1
  have ru : M.bondsBetween (u 0) (u 1) = 1 := (hrail 0).1
  have rw' : M.bondsBetween (w 0) (w 1) = 1 := (hrail 0).2.1
  have n1 := hne 0 1 h01
  have n2 := hne'' 0 0
  have n3 := hne'' 0 1
  have n4 := hne'' 1 0
  have n5 := hne'' 1 1
  have n6 := hne' 0 1 h01
  have sym := bondsBetween_symm M
  -- degrees of `u 0` and `u 1`
  have d0 := deg_eq_three hloop (a := u 0) (b := w 0) (c := u 1) (d := w 1) n2 n1 n3 n4.symm n6 n5
    (by rw [hs])
  have d1 : M.deg (u 1) = M.bondsBetween (u 1) (u 0) + M.bondsBetween (u 1) (w 1) + M.bondsBetween (u 1) (w 0) :=
    deg_eq_three hloop (a := u 1) (b := u 0) (c := w 1) (d := w 0) n1.symm n5 n4 n3 n2 n6.symm
      (by rw [hs]; ext z; simp only [mem_insert, mem_singleton]; tauto)
  have e0 := hreg (u 0) (by rw [hs]; simp)
  have e1 := hreg (u 1) (by rw [hs]; simp)
  refine ⟨u 0, w 0, u 1, w 1, n2, n1, n3, n4.symm, n6, n5, hs, r0, r1, ru, ?_, ?_, rw'⟩
  · linarith [d0, e0, r0, ru]
  · linarith [d1, e1, r1, ru, sym (u 1) (u 0), sym (u 1) (w 0)]

end WaveTurbulence.FinalCountG8
