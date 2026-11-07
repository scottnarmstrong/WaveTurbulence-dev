/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionComponentEquiv
import Mathlib.Tactic

/-! # Small bridgeless cuts connect all surviving boundary atoms globally -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem boundary_neighbor_component_mem_new (M : Molecule V D) (Y : Finset V)
    {x : D} (hx : x ∈ Degen.boundaryDarts M Y) :
    Degen.residualComponent M Y (M.atom (M.mate x)) ∈ Degen.newComponents M Y := by
  classical
  have hx' := (mem_filter.mp hx).2
  have hout : M.atom (M.mate x) ∈ M.atoms \ Y := mem_sdiff.mpr ⟨M.atom_mem _,hx'.2⟩
  have href : M.atom (M.mate x) ∈ Degen.residualComponent M Y (M.atom (M.mate x)) :=
    (Degen.mem_residualComponent M Y _ _).mpr ⟨M.atom_mem _,hx'.2,Relation.EqvGen.refl _⟩
  apply mem_filter.mpr
  refine ⟨mem_image.mpr ⟨_,hout,rfl⟩,?_⟩
  refine ⟨M.mate x,mem_filter.mpr ⟨mem_univ _,href,?_⟩⟩
  rw [M.mate_mate]
  intro hi
  exact ((Degen.mem_residualComponent M Y _ _).mp hi).2.1 hx'.1

theorem boundary_neighbors_connected_of_small (M : Molecule V D) (Y : Finset V)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (hsmall : (Degen.boundaryDarts M Y).card ≤ 3)
    {x y : D} (hx : x ∈ Degen.boundaryDarts M Y) (hy : y ∈ Degen.boundaryDarts M Y) :
    (Degen.eraseAtoms M Y).SameComponent (M.atom (M.mate x)) (M.atom (M.mate y)) := by
  classical
  have hc := Degen.two_mul_card_newComponents_le M hbridge Y
  have hcard : (Degen.newComponents M Y).card ≤ 1 := by omega
  have he := card_le_one.mp hcard _ (boundary_neighbor_component_mem_new M Y hx)
    _ (boundary_neighbor_component_mem_new M Y hy)
  have href : M.atom (M.mate y) ∈ Degen.residualComponent M Y (M.atom (M.mate y)) :=
    (Degen.mem_residualComponent M Y _ _).mpr
      ⟨M.atom_mem _,(mem_filter.mp hy).2.2,Relation.EqvGen.refl _⟩
  rw [← he] at href
  exact (Degen.eraseAtoms_sameComponent_iff M Y _ _).mpr
    ((Degen.mem_residualComponent M Y _ _).mp href).2.2

/-- This local cut statement preserves the global component quotient,
without connectedness of unrelated old components. -/
theorem numComponents_eraseAtoms_eq_of_small_boundary (M : Molecule V D) (Y : Finset V)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (hsmall : (Degen.boundaryDarts M Y).card ≤ 3)
    (hne : (Degen.boundaryDarts M Y).Nonempty)
    (hYconn : ∀ a ∈ Y,∀ c ∈ Y,M.SameComponent a c) :
    (Degen.eraseAtoms M Y).numComponents = M.numComponents := by
  obtain ⟨x,hx⟩ := hne
  have hx' := (mem_filter.mp hx).2
  apply numComponents_eraseAtoms_eq_of_cut_paths M Y (M.atom (M.mate x))
    (mem_sdiff.mpr ⟨M.atom_mem _,hx'.2⟩)
  · intro a ha
    exact Relation.EqvGen.trans _ _ _ (hYconn a ha _ hx'.1)
      (Relation.EqvGen.rel _ _ ⟨x,rfl,rfl⟩)
  · intro y hy
    exact boundary_neighbors_connected_of_small M Y hbridge hsmall hx hy

end WaveTurbulence.Mole.AppbAlgorithm
