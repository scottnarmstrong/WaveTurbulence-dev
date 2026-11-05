/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Cut
import Mathlib.Tactic

/-! # DH21 Lemma 9.13: a newly separated component has at least two boundary bonds -/

@[expose] public section
open Finset

namespace WaveTurbulence.Degen

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Adjacency after deleting one undirected bond (both of its darts). -/
def AdjWithoutBond (M : Molecule V D) (e : D) (u v : V) : Prop :=
  ∃ x : D, M.atom x = u ∧ M.atom (M.mate x) = v ∧ x ≠ e ∧ x ≠ M.mate e

/-- A bond is a bridge exactly when its endpoints disconnect upon deletion.
This is the usual endpoint characterization of DH21 Definition 9.12. -/
def IsBridge (M : Molecule V D) (e : D) : Prop :=
  ¬ Relation.EqvGen (AdjWithoutBond M e) (M.atom e) (M.atom (M.mate e))

/-- A cut with one boundary dart identifies an actual bridge, including
in a molecule with self-loops and multiple bonds. -/
theorem isBridge_of_single_boundary (M : Molecule V D) (S : Finset V) {e : D}
    (he : boundaryDarts M S = {e}) : IsBridge M e := by
  have hemem : M.atom e ∈ S ∧ M.atom (M.mate e) ∉ S := by
    have hh : e ∈ boundaryDarts M S := by rw [he]; exact mem_singleton_self e
    simpa only [boundaryDarts, mem_filter, mem_univ, true_and] using hh
  have hcross (x : D) (hx : M.atom x ∈ S) (hy : M.atom (M.mate x) ∉ S) : x = e := by
    have hh : x ∈ boundaryDarts M S := by simp only [boundaryDarts, mem_filter, mem_univ, true_and]; exact ⟨hx, hy⟩
    rw [he] at hh
    exact mem_singleton.mp hh
  have hstep (u v : V) (h : AdjWithoutBond M e u v) : u ∈ S ↔ v ∈ S := by
    obtain ⟨x, rfl, rfl, hx, hx'⟩ := h
    constructor
    · intro hin
      by_contra hout
      exact hx (hcross x hin hout)
    · intro hin
      by_contra hout
      have hh : M.mate x = e := hcross (M.mate x) hin (by simpa only [M.mate_mate] using hout)
      have hm := congrArg M.mate hh
      rw [M.mate_mate] at hm
      exact hx' hm
  have hpreserve : ∀ u v, Relation.EqvGen (AdjWithoutBond M e) u v → (u ∈ S ↔ v ∈ S) := by
    intro u v hpath
    induction hpath with
    | rel u v h => exact hstep u v h
    | refl u => rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  intro hpath
  exact hemem.2 ((hpreserve _ _ hpath).mp hemem.1)

/-- DH21 Lemma 9.13, the cut form: in a bridgeless molecule every nonempty
boundary has at least two bonds. This also applies to every new component
after removing atoms, since its boundary is nonempty by newness. -/
theorem two_le_boundary_card (M : Molecule V D) (hbridge : ∀ e : D, ¬IsBridge M e)
    (S : Finset V) (hne : (boundaryDarts M S).Nonempty) :
    2 ≤ (boundaryDarts M S).card := by
  by_contra hlt
  have hcard : (boundaryDarts M S).card = 1 := by
    have hp := Finset.card_pos.mpr hne
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  exact hbridge e (isBridge_of_single_boundary M S he)

end WaveTurbulence.Degen
