/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Bridges
import Mathlib.Tactic

/-! # Actual residual components and DH21 Lemma 9.13 -/

@[expose] public section
open Finset

namespace WaveTurbulence.Degen

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Adjacency of the induced molecule after deleting atoms `Y`. -/
def ResidualAdj (M : Molecule V D) (Y : Finset V) (u v : V) : Prop :=
  u ∉ Y ∧ v ∉ Y ∧ M.Adj u v

/-- The actual residual component containing `v`; used only for `v∉Y`. -/
noncomputable def residualComponent (M : Molecule V D) (Y : Finset V) (v : V) : Finset V := by
  classical
  exact M.atoms.filter fun u => u ∉ Y ∧ Relation.EqvGen (ResidualAdj M Y) v u

@[simp] theorem mem_residualComponent (M : Molecule V D) (Y : Finset V) (v u : V) :
    u ∈ residualComponent M Y v ↔
    u ∈ M.atoms ∧ u ∉ Y ∧ Relation.EqvGen (ResidualAdj M Y) v u := by
  classical
  simp only [residualComponent, mem_filter]

/-- The distinct components newly separated by deletion, excluding untouched
old components (which have empty boundary). -/
noncomputable def newComponents (M : Molecule V D) (Y : Finset V) : Finset (Finset V) := by
  classical
  exact ((M.atoms \ Y).image (residualComponent M Y)).filter fun S => (boundaryDarts M S).Nonempty

/-- Every boundary bond of a residual component ends at a removed atom. -/
theorem residual_boundary_ends_in_removed (M : Molecule V D) (Y : Finset V) (v : V)
    {x : D} (hx : x ∈ boundaryDarts M (residualComponent M Y v)) :
    M.atom (M.mate x) ∈ Y := by
  have hx' : M.atom x ∈ residualComponent M Y v ∧ M.atom (M.mate x) ∉ residualComponent M Y v := by
    simpa only [boundaryDarts, mem_filter, mem_univ, true_and] using hx
  have hp := (mem_residualComponent M Y v (M.atom x)).mp hx'.1
  by_contra hn
  apply hx'.2
  apply (mem_residualComponent M Y v (M.atom (M.mate x))).mpr
  refine ⟨M.atom_mem (M.mate x), hn, ?_⟩
  exact Relation.EqvGen.trans _ _ _ hp.2.2
    (Relation.EqvGen.rel _ _ ⟨hp.2.1, hn, x, rfl, rfl⟩)

/-- Two components which intersect are equal. -/
theorem residualComponent_eq_of_mem (M : Molecule V D) (Y : Finset V) {v w z : V}
    (hzv : z ∈ residualComponent M Y v) (hzw : z ∈ residualComponent M Y w) :
    residualComponent M Y v = residualComponent M Y w := by
  have hvz := ((mem_residualComponent M Y v z).mp hzv).2.2
  have hwz := ((mem_residualComponent M Y w z).mp hzw).2.2
  ext u
  simp only [mem_residualComponent]
  constructor
  · rintro ⟨hu, hY, hvu⟩
    exact ⟨hu, hY, Relation.EqvGen.trans _ _ _ hwz
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hvz) hvu)⟩
  · rintro ⟨hu, hY, hwu⟩
    exact ⟨hu, hY, Relation.EqvGen.trans _ _ _ hvz
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hwz) hwu)⟩

/-- Distinct actual new components have disjoint boundary darts. -/
theorem newComponents_boundary_disjoint (M : Molecule V D) (Y : Finset V) :
    (newComponents M Y : Set (Finset V)).PairwiseDisjoint (boundaryDarts M) := by
  classical
  intro S hS T hT hST
  obtain ⟨hS, _⟩ := mem_filter.mp hS
  obtain ⟨hT, _⟩ := mem_filter.mp hT
  obtain ⟨v, _, rfl⟩ := mem_image.mp hS
  obtain ⟨w, _, rfl⟩ := mem_image.mp hT
  apply disjoint_left.mpr
  intro x hx hy
  have hx' : M.atom x ∈ residualComponent M Y v := (mem_filter.mp hx).2.1
  have hy' : M.atom x ∈ residualComponent M Y w := (mem_filter.mp hy).2.1
  exact hST (residualComponent_eq_of_mem M Y hx' hy')

/-- The union of component boundaries injects into the boundary at the
removed atoms, by the bond involution. -/
theorem sum_newComponents_boundary_card_le (M : Molecule V D) (Y : Finset V) :
    ∑ S ∈ newComponents M Y, (boundaryDarts M S).card ≤ (boundaryDarts M Y).card := by
  classical
  let B := (newComponents M Y).biUnion (boundaryDarts M)
  have hinj : Function.Injective M.mate := fun x y h => by
    have he := congrArg M.mate h
    simpa only [M.mate_mate] using he
  have hsub : B.image M.mate ⊆ boundaryDarts M Y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨S, hS, hy⟩ := mem_biUnion.mp hy
    obtain ⟨hS, _⟩ := mem_filter.mp hS
    obtain ⟨v, _, rfl⟩ := mem_image.mp hS
    have hY := residual_boundary_ends_in_removed M Y v hy
    have hyS := (mem_filter.mp hy).2.1
    have hnY := ((mem_residualComponent M Y v (M.atom y)).mp hyS).2.1
    simp only [boundaryDarts, mem_filter, mem_univ, true_and, M.mate_mate]
    exact ⟨hY, hnY⟩
  calc
    _ = B.card := (card_biUnion (newComponents_boundary_disjoint M Y)).symm
    _ = (B.image M.mate).card := (card_image_of_injective B hinj).symm
    _ ≤ _ := card_le_card hsub

/-- DH21 Lemma 9.13 in full, with actual residual components: twice the
number of new components is at most the number of crossing bonds. -/
theorem two_mul_card_newComponents_le (M : Molecule V D)
    (hbridge : ∀ e : D, ¬IsBridge M e) (Y : Finset V) :
    2 * (newComponents M Y).card ≤ (boundaryDarts M Y).card := by
  classical
  calc
    _ = ∑ _S ∈ newComponents M Y, 2 := by simp; omega
    _ ≤ ∑ S ∈ newComponents M Y, (boundaryDarts M S).card := by
      apply sum_le_sum
      intro S hS
      exact two_le_boundary_card M hbridge S (mem_filter.mp hS).2
    _ ≤ _ := sum_newComponents_boundary_card_le M Y

end WaveTurbulence.Degen
