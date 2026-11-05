/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-!
# Full-degree barriers and absence of saturated atomic groups

DH23 Lemma 4.11: a path can leave a block only at a joint. The central
local fact follows from the actual half-edge degree bound, including loops.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- If an atom already has all four incidences inside S, none can leave S. -/
theorem full_degree_no_exit (hM : M.IsMolecule) {S : Finset V} {v : V}
    (hv : v ∈ M.atoms) (hd : M.degIn S v = 4) {x : D} (hx : M.atom x = v) :
    M.atom (M.mate x) ∈ S := by
  have he : (M.dartsAt v).filter (M.InGroup S) = M.dartsAt v := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    have h := deg_le_four M hM hv
    change M.deg v ≤ M.degIn S v
    omega
  have hmem : x ∈ (M.dartsAt v).filter (M.InGroup S) := by
    rw [he]
    exact (mem_dartsAt M v x).mpr hx
  exact (Finset.mem_filter.mp hmem).2.2

/-- An interior atom of a block can only be adjacent to atoms of that block. -/
theorem block_interior_adj_mem (hM : M.IsMolecule) {S : Finset V} {j1 j2 v z : V}
    (hB : M.IsBlock S j1 j2) (hv : v ∈ S) (h1 : v ≠ j1) (h2 : v ≠ j2)
    (ha : M.Adj v z) : z ∈ S := by
  obtain ⟨x,hx,hz⟩ := ha
  rw [← hz]
  exact full_degree_no_exit M hM (hB.1 hv) (hB.2.2.2.2.2.2.2.2.1 v hv h1 h2) hx

/-- A group with degree four at every atom is impossible in a molecule.
This is the saturated-union contradiction in DH23 Lemma 4.11. -/
theorem no_saturated_group (hM : M.IsMolecule) {S : Finset V}
    (hS : S ⊆ M.atoms) (hne : S.Nonempty) (hd : ∀ v ∈ S, M.degIn S v = 4) : False := by
  have closed : ∀ {u v}, u ∈ S → M.Adj u v → v ∈ S := by
    intro u v hu ha
    obtain ⟨x,hx,hv⟩ := ha
    rw [← hv]
    exact full_degree_no_exit M hM (hS hu) (hd u hu) hx
  have path_mem : ∀ {u v}, M.SameComponent u v → (u ∈ S ↔ v ∈ S) := by
    intro u v hp
    induction hp with
    | rel a b hab => exact ⟨fun ha => closed ha hab,fun hb => closed hb (adj_symmetric M hab)⟩
    | refl => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  obtain ⟨v,hv⟩ := hne
  obtain ⟨z,hz,hvz,hzd⟩ := hM.2 v (hS hv)
  have hzS := (path_mem hvz).mp hv
  have hle := degIn_le_deg M S z
  have hfour := deg_le_four M hM hz
  have hzin := hd z hzS
  exact hzd (by omega)

omit [DecidableEq V] [Fintype D] in
/-- Adjacency in the actual induced half-edge carrier. -/
theorem induced_adj_iff (S : Finset V) (u v : V) :
    (induced M S).Adj u v ↔ M.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  constructor
  · rintro ⟨x,hx,hv⟩
    exact ⟨⟨x.1,hx,hv⟩,hx ▸ x.2.1,hv ▸ x.2.2⟩
  · rintro ⟨⟨x,hx,hv⟩,hu,hvS⟩
    exact ⟨⟨x,hx.symm ▸ hu,hv.symm ▸ hvS⟩,hx,hv⟩

/-- Paths constrained to T cannot cross the boundary of S at an atom that
has all four incidences in S. -/
theorem induced_path_barrier (hM : M.IsMolecule) {S T : Finset V}
    (hS : S ⊆ M.atoms) (hd : ∀ u ∈ S, u ∈ T → M.degIn S u = 4)
    {u v : V} (hp : (induced M T).SameComponent u v) : u ∈ S ↔ v ∈ S := by
  have closed : ∀ {a b}, a ∈ S → (induced M T).Adj a b → b ∈ S := by
    intro a b ha hab
    obtain ⟨⟨x,hx,hb⟩,haT,_hbT⟩ := (induced_adj_iff M T a b).mp hab
    rw [← hb]
    exact full_degree_no_exit M hM (hS ha) (hd a ha haT) hx
  induction hp with
  | rel a b hab => exact ⟨fun ha => closed ha hab,
      fun hb => closed hb (adj_symmetric (induced M T) hab)⟩
  | refl => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

/-- DH23 Lemma 4.11, the geometric part of case (a): two incomparable
blocks with the same joints have no common interior atom. -/
theorem block_same_joints_intersection (hM : M.IsMolecule) {A B : Finset V} {j1 j2 : V}
    (hA : M.IsBlock A j1 j2) (hB : M.IsBlock B j1 j2) (hnot : ¬ A ⊆ B)
    (hconn : ∀ u ∈ A \ {j1,j2}, ∀ v ∈ A \ {j1,j2},
      (induced M (A \ {j1,j2})).SameComponent u v) :
    A ∩ B = {j1,j2} := by
  ext u
  constructor
  · intro hu
    obtain ⟨huA,huB⟩ := Finset.mem_inter.mp hu
    by_contra hj
    have huT : u ∈ A \ {j1,j2} := Finset.mem_sdiff.mpr ⟨huA,hj⟩
    obtain ⟨v,hvA,hvB⟩ := Finset.not_subset.mp hnot
    have hvT : v ∈ A \ {j1,j2} := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hvA,?_⟩
      intro hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hvB hB.2.1
      · exact hvB hB.2.2.1
    have hd : ∀ z ∈ B, z ∈ A \ {j1,j2} → M.degIn B z = 4 := by
      intro z hz hzT
      have hn := (Finset.mem_sdiff.mp hzT).2
      have hz1 : z ≠ j1 := fun he => hn (Finset.mem_insert.mpr (Or.inl he))
      have hz2 : z ≠ j2 := fun he => hn (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))
      exact hB.2.2.2.2.2.2.2.2.1 z hz hz1 hz2
    exact hvB ((induced_path_barrier M hM hB.1 hd (hconn u huT v hvT)).mp huB)
  · intro hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hA.2.1,hB.2.1⟩
    · exact Finset.mem_inter.mpr ⟨hA.2.2.1,hB.2.2.1⟩

end WaveTurbulence.Mole
