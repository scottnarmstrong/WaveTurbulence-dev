/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! # DH23 Proposition 10.3: the terminal simple graph is K4

The half-edge incidence map is injective when there are no loops or
parallel bonds. Handshaking then gives the actual rank bound and the
four-vertex complete-graph classification, without assumed topology.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- In a loopless graph with at most one bond per distinct pair, incident
darts have distinct other endpoints. -/
theorem otherEndpoint_injOn_dartsAt (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) (a : V) :
    Set.InjOn (fun x => M.atom (M.mate x)) (M.dartsAt a) := by
  intro x hx y hy hxy
  have hxa : M.atom x = a := (Mole.mem_dartsAt M a x).mp hx
  have hab : a ≠ M.atom (M.mate x) := hxa ▸ hloop x
  have hc : (neighborDarts M a (M.atom (M.mate x))).card ≤ 1 := by
    rw [card_neighborDarts M hab]
    exact hsimple _ _ hab
  apply Finset.card_le_one.mp hc
  · exact mem_filter.mpr ⟨hx,rfl⟩
  · exact mem_filter.mpr ⟨hy,hxy.symm⟩

/-- Every actual degree is bounded by the number of other atoms. -/
theorem degree_le_card_erase (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) (a : V) :
    M.deg a ≤ (M.atoms.erase a).card := by
  have hsub : (M.dartsAt a).image (fun x => M.atom (M.mate x)) ⊆ M.atoms.erase a := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
    have hxa := (Mole.mem_dartsAt M a x).mp hx
    exact mem_erase.mpr ⟨by simpa only [← hxa] using (hloop x).symm,M.atom_mem _⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn (otherEndpoint_injOn_dartsAt M hloop hsimple a)] at hc
  exact hc

/-- A nonempty simple half-edge graph with minimum degree three has at
least four actual atoms. -/
theorem four_le_card_atoms_of_degree_ge_three (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a) :
    4 ≤ M.atoms.card := by
  obtain ⟨a,ha⟩ := hne
  have hd := degree_le_card_erase M hloop hsimple a
  have he := card_erase_of_mem ha
  have hm := hmin a ha
  omega

/-- Exact handshaking lower bound for graphs of minimum degree three. -/
theorem three_mul_card_atoms_le_two_mul_bonds (M : Molecule V D)
    (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a) :
    3 * M.atoms.card ≤ 2 * M.bonds.card := by
  have hs : (∑ _a ∈ M.atoms, (3 : ℕ)) ≤ ∑ a ∈ M.atoms, M.deg a := sum_le_sum hmin
  rw [Finset.sum_const_nat (fun _ _ => rfl),Mole.sum_degrees_eq_two_mul_bonds] at hs
  omega

/-- DH23 Proposition 10.3 search invariant: a connected nontrivial simple
graph of minimum degree three has circuit rank at least three. -/
theorem circuitRank_ge_three_of_simple_min_degree (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) :
    3 ≤ M.circuitRank := by
  have hv := four_le_card_atoms_of_degree_ge_three M hloop hsimple hne hmin
  have hh := three_mul_card_atoms_le_two_mul_bonds M hmin
  have hf := Mole.numComponents_eq_one M hne hconn
  rw [Molecule.circuitRank,hf]
  omega

/-- Rank three forces exactly four vertices and degree three everywhere. -/
theorem card_atoms_and_degree_of_simple_rank_three (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hrank : M.circuitRank = 3) :
    M.atoms.card = 4 ∧ ∀ a ∈ M.atoms, M.deg a = 3 := by
  have hv := four_le_card_atoms_of_degree_ge_three M hloop hsimple hne hmin
  have hh := three_mul_card_atoms_le_two_mul_bonds M hmin
  have hf := Mole.numComponents_eq_one M hne hconn
  have hr := hrank
  rw [Molecule.circuitRank,hf] at hr
  have hc : M.atoms.card = 4 := by omega
  refine ⟨hc,fun a ha => ?_⟩
  have hd := degree_le_card_erase M hloop hsimple a
  have he := card_erase_of_mem ha
  have hm := hmin a ha
  omega

/-- The actual half-edge rank-three graph is K4: four atoms, degree three,
and an actual bond between every two distinct atoms. -/
theorem complete_of_simple_rank_three (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hne : M.atoms.Nonempty) (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (hrank : M.circuitRank = 3) :
    M.atoms.card = 4 ∧ (∀ a ∈ M.atoms, M.deg a = 3) ∧
      ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.Adj a b := by
  obtain ⟨hc,hd⟩ := card_atoms_and_degree_of_simple_rank_three M hloop hsimple hne hmin hconn hrank
  refine ⟨hc,hd,fun a ha b hb hab => ?_⟩
  have hsub : (M.dartsAt a).image (fun x => M.atom (M.mate x)) ⊆ M.atoms.erase a := by
    intro c hmem
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hmem
    have hxa := (Mole.mem_dartsAt M a x).mp hx
    exact mem_erase.mpr ⟨by simpa only [← hxa] using (hloop x).symm,M.atom_mem _⟩
  have himg : (M.dartsAt a).image (fun x => M.atom (M.mate x)) = M.atoms.erase a := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn (otherEndpoint_injOn_dartsAt M hloop hsimple a)]
    have he := card_erase_of_mem ha
    have hda := hd a ha
    change (M.atoms.erase a).card ≤ M.deg a
    omega
  have hbimg : b ∈ (M.dartsAt a).image (fun x => M.atom (M.mate x)) := by
    rw [himg]
    exact mem_erase.mpr ⟨hab.symm,hb⟩
  obtain ⟨x,hx,hxb⟩ := mem_image.mp hbimg
  exact ⟨x,(Mole.mem_dartsAt M a x).mp hx,hxb⟩

end WaveTurbulence.MoleProp
