/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-!
# Basic half-edge molecule calculus

TARGET Definition 7.1 (`defmol`, L1295): degrees, directed bond representatives,
undirected adjacency and component paths. All statements use the exact B2
molecule carrier and handle multiple bonds and self-loops.
-/

public section

namespace WaveTurbulence.Mole

open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem mem_dartsAt (v : V) (x : D) : x ∈ M.dartsAt v ↔ M.atom x = v := by
  simp only [Molecule.dartsAt,mem_filter,mem_univ,true_and]

omit [DecidableEq V] [Fintype D] in
theorem mate_injective : Function.Injective M.mate :=
  Function.Involutive.injective M.mate_mate

/-- TARGET `defmol`: total degree is outgoing plus incoming degree,
including the two separate darts of a self-loop. -/
theorem outdeg_add_indeg (v : V) : M.outdeg v+M.indeg v = M.deg v := by
  have he := (M.dartsAt v).card_filter_add_card_filter_not (fun x => M.out x = true)
  simpa only [Molecule.outdeg,Molecule.indeg,Molecule.deg,Bool.not_eq_true] using he

/-- TARGET `defmol`(i): every atom of a molecule has degree at most four. -/
theorem deg_le_four (hM : M.IsMolecule) {v : V} (hv : v ∈ M.atoms) : M.deg v ≤ 4 := by
  have hdegrees := hM.1 v hv
  have he := outdeg_add_indeg M v
  omega

omit [DecidableEq V] in
/-- Incoming and outgoing dart sets have the same cardinality by the
actual fixed-point-free mate involution. -/
theorem card_incoming_eq_bonds :
    (Finset.univ.filter (fun x : D => M.out x = false)).card = M.bonds.card := by
  apply Finset.card_bij (fun x _hx => M.mate x)
  · intro x hx
    have hxout := (Finset.mem_filter.mp hx).2
    simp only [Molecule.bonds,mem_filter,mem_univ,true_and,M.out_mate,hxout,Bool.not_false]
  · intro x hx y hy hxy
    exact mate_injective M hxy
  · intro y hy
    have hyout := (Finset.mem_filter.mp hy).2
    refine ⟨M.mate y,?_,M.mate_mate y⟩
    simp only [mem_filter,mem_univ,true_and,M.out_mate,hyout,Bool.not_true]

omit [DecidableEq V] in
/-- TARGET `defmol`: there are exactly two darts per bond. -/
theorem two_mul_card_bonds : 2*M.bonds.card = Fintype.card D := by
  have he := (Finset.univ : Finset D).card_filter_add_card_filter_not (fun x => M.out x = true)
  have hcard := card_incoming_eq_bonds M
  simp only [Bool.not_eq_true,Finset.card_univ] at he
  change M.bonds.card+(Finset.univ.filter (fun x : D => M.out x = false)).card = Fintype.card D at he
  omega

/-- TARGET `defmol`: the sum of atom degrees is twice the number of bonds. -/
theorem sum_degrees_eq_two_mul_bonds : ∑ v ∈ M.atoms, M.deg v = 2*M.bonds.card := by
  have he := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset D))
    (t := M.atoms) (f := M.atom) (fun x _hx => M.atom_mem x)
  have hsum : ∑ v ∈ M.atoms, M.deg v = Fintype.card D := by
    simpa only [Molecule.deg,Molecule.dartsAt,Finset.card_univ] using he.symm
  exact hsum.trans (two_mul_card_bonds M).symm

omit [DecidableEq V] [Fintype D] in
/-- TARGET `defmol`: adjacency ignores orientation. -/
theorem adj_symmetric {u v : V} (huv : M.Adj u v) : M.Adj v u := by
  obtain ⟨x,hx,hy⟩ := huv
  exact ⟨M.mate x,hy,by rw [M.mate_mate]; exact hx⟩

omit [DecidableEq V] [Fintype D] in
theorem sameComponent_refl (v : V) : M.SameComponent v v := Relation.EqvGen.refl v

omit [DecidableEq V] [Fintype D] in
theorem sameComponent_symm {u v : V} (h : M.SameComponent u v) : M.SameComponent v u :=
  Relation.EqvGen.symm _ _ h

omit [DecidableEq V] [Fintype D] in
theorem sameComponent_trans {u v z : V} (h : M.SameComponent u v) (h' : M.SameComponent v z) :
    M.SameComponent u z := Relation.EqvGen.trans _ _ _ h h'

omit [DecidableEq V] [Fintype D] in
theorem sameComponent_of_adj {u v : V} (h : M.Adj u v) : M.SameComponent u v :=
  Relation.EqvGen.rel _ _ h

end WaveTurbulence.Mole
