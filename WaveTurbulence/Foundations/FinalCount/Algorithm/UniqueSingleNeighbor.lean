/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # A degree-three atom with a double bond has a unique single-bond partner -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

theorem single_neighbor_unique_of_double (M : Molecule V D) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d)
    (hdeg : M.deg a = 3) (hb : M.bondsBetween a b = 1)
    (hc : M.bondsBetween a c = 2) (hd : M.bondsBetween a d = 1) : d = b := by
  classical
  let A := (M.dartsAt a).filter fun x => M.atom (M.mate x) = b
  let C := (M.dartsAt a).filter fun x => M.atom (M.mate x) = c
  have hA : A.card = 1 := (bondsBetween_eq_card_darts M hab).symm.trans hb
  have hC : C.card = 2 := (bondsBetween_eq_card_darts M hac).symm.trans hc
  have hdis : Disjoint A C := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hbc ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
  have hsub : A ∪ C ⊆ M.dartsAt a := union_subset (filter_subset _ _) (filter_subset _ _)
  have hunion : A ∪ C = M.dartsAt a := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdis,hA,hC]
    exact hdeg.le
  have hdp : 0 < ((M.dartsAt a).filter fun x => M.atom (M.mate x) = d).card := by
    rw [← bondsBetween_eq_card_darts M had,hd]
    decide
  obtain ⟨x,hx⟩ := card_pos.mp hdp
  obtain ⟨hxa,hxd⟩ := mem_filter.mp hx
  have hxm : x ∈ A ∪ C := by rw [hunion]; exact hxa
  rcases mem_union.mp hxm with hxb | hxc
  · exact hxd.symm.trans (mem_filter.mp hxb).2
  · have hdc : d = c := hxd.symm.trans (mem_filter.mp hxc).2
    rw [hdc,hc] at hd
    omega

end WaveTurbulence.Mole.AppbAlgorithm
