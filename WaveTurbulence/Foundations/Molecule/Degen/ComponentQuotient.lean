/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Components
public import WaveTurbulence.Foundations.Molecule.Degen.Removal
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-! # Finite component sets represent the B2 component quotient exactly -/

@[expose] public section
open Finset

namespace WaveTurbulence.Degen

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def componentSet (M : Molecule V D) (v : V) : Finset V := by
  classical
  exact M.atoms.filter fun u => M.SameComponent v u

noncomputable def componentSets (M : Molecule V D) : Finset (Finset V) := by
  classical
  exact M.atoms.image (componentSet M)

@[simp] theorem mem_componentSet (M : Molecule V D) (v u : V) :
    u ∈ componentSet M v ↔ u ∈ M.atoms ∧ M.SameComponent v u := by
  classical
  simp only [componentSet, mem_filter]

theorem componentSet_eq_iff (M : Molecule V D) {u v : V} (hu : u ∈ M.atoms) :
    componentSet M u = componentSet M v ↔ M.SameComponent u v := by
  constructor
  · intro he
    have hh : u ∈ componentSet M u := by simp only [mem_componentSet]; exact ⟨hu, Relation.EqvGen.refl u⟩
    rw [he] at hh
    exact Relation.EqvGen.symm _ _ ((mem_componentSet M v u).mp hh).2
  · intro h
    ext z
    simp only [mem_componentSet]
    constructor
    · rintro ⟨hz, huz⟩
      exact ⟨hz, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) huz⟩
    · rintro ⟨hz, hvz⟩
      exact ⟨hz, Relation.EqvGen.trans _ _ _ h hvz⟩

/-- No alternate component count is substituted for the declared quotient. -/
theorem numComponents_eq_card_componentSets (M : Molecule V D) :
    M.numComponents = (componentSets M).card := by
  classical
  let Q := Quot (fun a b : M.atoms => M.Adj a.val b.val)
  let f : Q → {S // S ∈ componentSets M} := Quot.lift
    (fun a : M.atoms => ⟨componentSet M a.val, mem_image.mpr ⟨a.val, a.property, rfl⟩⟩)
    (by
      intro a b hab
      apply Subtype.ext
      exact (componentSet_eq_iff M a.property).mpr (Relation.EqvGen.rel _ _ hab))
  have hinj : Function.Injective f := by
    intro q q' he
    induction q using Quot.inductionOn with | h a =>
      induction q' using Quot.inductionOn with | h b =>
        have he' : componentSet M a.val = componentSet M b.val := congrArg Subtype.val he
        exact Mole.quotient_eq_of_sameComponent M ((componentSet_eq_iff M a.property).mp he') a.property b.property
  have hsurj : Function.Surjective f := by
    intro S
    obtain ⟨a, ha, he⟩ := mem_image.mp S.property
    refine ⟨Quot.mk _ ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact he
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa only [Molecule.numComponents, Q, Nat.card_eq_finsetCard] using hc

/-- The induced molecule's adjacency is exactly the residual adjacency. -/
theorem eraseAtoms_adj_iff (M : Molecule V D) (Y : Finset V) (u v : V) :
    (eraseAtoms M Y).Adj u v ↔ ResidualAdj M Y u v := by
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨x.property.1, x.property.2, x.val, rfl, rfl⟩
  · rintro ⟨hu, hv, x, hx, hy⟩
    refine ⟨⟨x, ?_, ?_⟩, hx, hy⟩
    · simpa only [hx] using hu
    · simpa only [hy] using hv

theorem eraseAtoms_sameComponent_iff (M : Molecule V D) (Y : Finset V) (u v : V) :
    (eraseAtoms M Y).SameComponent u v ↔ Relation.EqvGen (ResidualAdj M Y) u v := by
  have he : (eraseAtoms M Y).Adj = ResidualAdj M Y := by
    funext a b
    exact propext (eraseAtoms_adj_iff M Y a b)
  unfold Molecule.SameComponent
  rw [he]

theorem eraseAtoms_componentSet (M : Molecule V D) (Y : Finset V) (v : V) :
    componentSet (eraseAtoms M Y) v = residualComponent M Y v := by
  ext u
  simp only [mem_componentSet, eraseAtoms_sameComponent_iff, mem_residualComponent]
  change ((u ∈ M.atoms \ Y) ∧ _) ↔ _
  simp only [mem_sdiff, and_assoc]

/-- An empty cut boundary makes membership constant along every original
component path. -/
theorem sameComponent_mem_iff_of_boundary_empty (M : Molecule V D) (S : Finset V)
    (hS : boundaryDarts M S = ∅) {u v : V} (hpath : M.SameComponent u v) :
    u ∈ S ↔ v ∈ S := by
  have hstep (a b : V) (hab : M.Adj a b) : a ∈ S ↔ b ∈ S := by
    obtain ⟨x, rfl, rfl⟩ := hab
    constructor
    · intro hx
      by_contra hy
      have hb : x ∈ boundaryDarts M S := by
        simp only [boundaryDarts, mem_filter, mem_univ, true_and]
        exact ⟨hx, hy⟩
      rw [hS] at hb
      simpa only [Finset.notMem_empty] using hb
    · intro hx
      by_contra hy
      have hb : M.mate x ∈ boundaryDarts M S := by
        simp only [boundaryDarts, mem_filter, mem_univ, true_and, M.mate_mate]
        exact ⟨hx, hy⟩
      rw [hS] at hb
      simpa only [Finset.notMem_empty] using hb
  induction hpath with
  | rel a b h => exact hstep a b h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih ih' => exact ih.trans ih'

/-- Every surviving component of a connected molecule touches the deleted
nonempty atom set. Thus the “new” qualification in DH21 is exact. -/
theorem residual_boundary_nonempty_of_connected (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (Y : Finset V) (hY : Y.Nonempty) (hYM : Y ⊆ M.atoms)
    {v : V} (hv : v ∈ M.atoms \ Y) :
    (boundaryDarts M (residualComponent M Y v)).Nonempty := by
  classical
  by_contra hn
  have he : boundaryDarts M (residualComponent M Y v) = ∅ := not_nonempty_iff_eq_empty.mp hn
  obtain ⟨y, hy⟩ := hY
  have hv' := mem_sdiff.mp hv
  have hvmem : v ∈ residualComponent M Y v :=
    (mem_residualComponent M Y v v).mpr ⟨hv'.1, hv'.2, Relation.EqvGen.refl v⟩
  have hpath := hconn v hv'.1 y (hYM hy)
  have hymem := (sameComponent_mem_iff_of_boundary_empty M _ he hpath).mp hvmem
  exact ((mem_residualComponent M Y v y).mp hymem).2.1 hy

/-- Actual B2 component quotient after removing atoms from a connected
molecule is counted by the concrete residual components, without a
separate assumed component-count identity. -/
theorem numComponents_eraseAtoms_eq_card_newComponents (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (Y : Finset V) (hY : Y.Nonempty) (hYM : Y ⊆ M.atoms) :
    (eraseAtoms M Y).numComponents = (newComponents M Y).card := by
  classical
  rw [numComponents_eq_card_componentSets]
  congr 1
  have he : componentSets (eraseAtoms M Y) = (M.atoms \ Y).image (residualComponent M Y) := by
    unfold componentSets
    change (M.atoms \ Y).image (componentSet (eraseAtoms M Y)) = _
    congr 1
    funext v
    exact eraseAtoms_componentSet M Y v
  rw [he]
  unfold newComponents
  symm
  apply filter_eq_self.mpr
  intro S hS
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hS
  exact residual_boundary_nonempty_of_connected M hconn Y hY hYM hv

end WaveTurbulence.Degen
