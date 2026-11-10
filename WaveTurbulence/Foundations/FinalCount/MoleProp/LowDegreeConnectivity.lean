/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # Low-degree removal in bridgeless half-edge graphs

DH23 Proposition 10.3 only needs connectivity after deleting the chosen
degree-three atom. No assertion about arbitrary degree-four articulations,
or absence of beta cuts, is required.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The singleton cut has no more boundary darts than incident darts;
loops need no special exclusion. -/
theorem boundary_singleton_card_le_degree (M : Molecule V D) (v : V) :
    (boundaryDarts M {v}).card ≤ M.deg v := by
  apply card_le_card
  intro x hx
  have h := (mem_filter.mp hx).2.1
  exact (Mole.mem_dartsAt M v x).mpr (mem_singleton.mp h)

/-- Without bridges, deleting an atom of degree at most three produces
at most one residual component with a boundary at that atom. -/
theorem card_newComponents_singleton_le_one (M : Molecule V D)
    (hbridge : ∀ e, ¬Degen.IsBridge M e) {v : V} (hdeg : M.deg v ≤ 3) :
    (newComponents M {v}).card ≤ 1 := by
  have hc := two_mul_card_newComponents_le M hbridge ({v} : Finset V)
  have hb := boundary_singleton_card_le_degree M v
  omega

/-- Every surviving vertex in the old component of the removed atom
belongs to an actual residual component touching that atom. -/
theorem residualComponent_mem_newComponents_of_sameComponent (M : Molecule V D)
    {v u : V} (_hv : v ∈ M.atoms) (hu : u ∈ M.atoms) (huv : u ≠ v)
    (hpath : M.SameComponent u v) :
    residualComponent M {v} u ∈ newComponents M {v} := by
  classical
  have huself : u ∈ residualComponent M {v} u := by
    exact (mem_residualComponent M {v} u u).mpr
      ⟨hu,by simpa only [mem_singleton] using huv,Relation.EqvGen.refl u⟩
  have hboundary : (boundaryDarts M (residualComponent M {v} u)).Nonempty := by
    by_contra hn
    have he : boundaryDarts M (residualComponent M {v} u) = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hvmem := (sameComponent_mem_iff_of_boundary_empty M _ he hpath).mp huself
    have hvnot := ((mem_residualComponent M {v} u v).mp hvmem).2.1
    exact hvnot (mem_singleton_self v)
  apply mem_filter.mpr
  refine ⟨mem_image.mpr ⟨u,?_,rfl⟩,hboundary⟩
  exact mem_sdiff.mpr ⟨hu,by simpa only [mem_singleton] using huv⟩

/-- The actual old component of a removed atom remains connected after
removing it, when its degree is at most three and no bond is a bridge. -/
theorem erase_low_degree_sameComponent (M : Molecule V D)
    (hbridge : ∀ e, ¬Degen.IsBridge M e) {v : V} (hv : v ∈ M.atoms)
    (hdeg : M.deg v ≤ 3) {u w : V}
    (hu : u ∈ M.atoms) (hw : w ∈ M.atoms) (huv : u ≠ v) (hwv : w ≠ v)
    (hupath : M.SameComponent u v) (hwpath : M.SameComponent w v) :
    (eraseAtoms M {v}).SameComponent u w := by
  classical
  have hc := card_newComponents_singleton_le_one M hbridge hdeg
  have huNew := residualComponent_mem_newComponents_of_sameComponent M hv hu huv hupath
  have hwNew := residualComponent_mem_newComponents_of_sameComponent M hv hw hwv hwpath
  have he := Finset.card_le_one.mp hc _ huNew _ hwNew
  have hwself : w ∈ residualComponent M {v} w :=
    (mem_residualComponent M {v} w w).mpr
      ⟨hw,by simpa only [mem_singleton] using hwv,Relation.EqvGen.refl w⟩
  rw [← he] at hwself
  exact (eraseAtoms_sameComponent_iff M {v} u w).mpr
    ((mem_residualComponent M {v} u w).mp hwself).2.2

/-- DH23 Proposition 10.3 R step: degree at most three suffices for
connectivity after removal in any connected bridgeless graph. The empty
post graph is allowed; no beta-cut hypothesis is needed. -/
theorem erase_low_degree_connected (M : Molecule V D)
    (hbridge : ∀ e, ¬Degen.IsBridge M e)
    (hconn : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, M.SameComponent u w)
    {v : V} (hv : v ∈ M.atoms) (hdeg : M.deg v ≤ 3) :
    ∀ u ∈ (eraseAtoms M {v}).atoms, ∀ w ∈ (eraseAtoms M {v}).atoms,
      (eraseAtoms M {v}).SameComponent u w := by
  intro u hu w hw
  change u ∈ M.atoms \ {v} at hu
  change w ∈ M.atoms \ {v} at hw
  obtain ⟨hu,huv⟩ := mem_sdiff.mp hu
  obtain ⟨hw,hwv⟩ := mem_sdiff.mp hw
  exact erase_low_degree_sameComponent M hbridge hv hdeg hu hw
    (by simpa only [mem_singleton] using huv) (by simpa only [mem_singleton] using hwv)
    (hconn u hu v hv) (hconn w hw v hv)

end WaveTurbulence.MoleProp
