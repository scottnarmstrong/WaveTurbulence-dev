/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Distinct incidences of an actual four-element star -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem quadruple_distinct_of_card {D : Type*} [DecidableEq D] {x y r s : D}
    (hcard : ({x,y,r,s} : Finset D).card=4) :
    x ≠ y ∧ x ≠ r ∧ x ≠ s ∧ y ≠ r ∧ y ≠ s ∧ r ≠ s := by
  have hx : x ∉ ({y,r,s} : Finset D) := by
    intro hm
    rw [insert_eq_of_mem hm] at hcard
    have hh := card_le_three (a := y) (b := r) (c := s)
    omega
  rw [card_insert_of_notMem hx] at hcard
  have hthree : ({y,r,s} : Finset D).card=3 := by omega
  obtain ⟨hyr,hys,hrs⟩ := card_triple_eq_three_iff.mp hthree
  simp only [mem_insert,mem_singleton,not_or] at hx
  exact ⟨hx.1,hx.2.1,hx.2.2,hyr,hys,hrs⟩

end WaveTurbulence.MoleProp
