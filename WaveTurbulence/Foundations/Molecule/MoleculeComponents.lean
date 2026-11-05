/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import Mathlib.Data.Quot
import Mathlib.Tactic

/-!
# Actual component quotient of a half-edge molecule

TARGET `defmol` L1295: the declared component count is the quotient by
undirected adjacency. This module identifies its equality relation with
the declared ambient path predicate and computes the connected case.
-/

public section

namespace WaveTurbulence.Mole
variable {V D : Type*} (M : Molecule V D)

/-- Any actual adjacency step has both endpoints among the atoms. -/
theorem adj_atoms {u v : V} (h : M.Adj u v) : u ∈ M.atoms ∧ v ∈ M.atoms := by
  obtain ⟨x,rfl,rfl⟩ := h
  exact ⟨M.atom_mem x,M.atom_mem (M.mate x)⟩

theorem sameComponent_mem_iff {u v : V} (h : M.SameComponent u v) :
    u ∈ M.atoms ↔ v ∈ M.atoms := by
  induction h with
  | rel u v h => exact iff_of_true (adj_atoms M h).1 (adj_atoms M h).2
  | refl u => rfl
  | symm u v _ ih => exact ih.symm
  | trans u v z _ _ ih ih' => exact ih.trans ih'

/-- Ambient component paths give equality in the actual atom quotient. -/
theorem quotient_eq_of_sameComponent {u v : V} (h : M.SameComponent u v)
    (hu : u ∈ M.atoms) (hv : v ∈ M.atoms) :
    Quot.mk (fun a b : M.atoms => M.Adj a.1 b.1) ⟨u,hu⟩ =
      Quot.mk (fun a b : M.atoms => M.Adj a.1 b.1) ⟨v,hv⟩ := by
  induction h with
  | rel u v huv => exact Quot.sound huv
  | refl u => rfl
  | symm u v huv ih => exact (ih hv hu).symm
  | trans u v z huv hvz ih ih' =>
    have hvm : v ∈ M.atoms := (sameComponent_mem_iff M huv).mp hu
    exact (ih hu hvm).trans (ih' hvm hv)

/-- Quotient equality is exactly the actual ambient component relation. -/
theorem quotient_eq_iff_sameComponent (u v : M.atoms) :
    Quot.mk (fun a b : M.atoms => M.Adj a.1 b.1) u =
      Quot.mk (fun a b : M.atoms => M.Adj a.1 b.1) v ↔ M.SameComponent u.1 v.1 := by
  constructor
  · intro h
    have hh := Quot.eqvGen_exact h
    clear h
    induction hh with
    | rel u v huv => exact Relation.EqvGen.rel _ _ huv
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v z _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  · intro h
    exact quotient_eq_of_sameComponent M h u.2 v.2

/-- A finite molecule has no more components than atoms. -/
theorem numComponents_le_card_atoms : M.numComponents ≤ M.atoms.card := by
  have hh := Nat.card_le_card_of_surjective
    (Quot.mk (fun a b : M.atoms => M.Adj a.1 b.1)) Quot.mk_surjective
  simpa only [Molecule.numComponents,Nat.card_eq_finsetCard] using hh

/-- A nonempty connected molecule has exactly one component. -/
theorem numComponents_eq_one (hne : M.atoms.Nonempty)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) : M.numComponents = 1 := by
  obtain ⟨v,hv⟩ := hne
  let v0 : M.atoms := ⟨v,hv⟩
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quot.mk _ v0,?_⟩
  intro q
  induction q using Quot.inductionOn with
  | h u => exact quotient_eq_of_sameComponent M (hconn u.1 u.2 v hv) u.2 hv

end WaveTurbulence.Mole
