/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineThinEmptyPairs
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
public import WaveTurbulence.Foundations.Molecule.VineCoreBondCounts
import Mathlib.Tactic

/-! # An empty expanded slot forces its doubled terminal pair to be absent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Propagate absence through a positive-length slot and its old doubled
terminal pair, without a short-length exception or full old-atom row. -/
theorem block_slot_double_end_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (hk : 1 ≤ k)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.2,s.2.2)) (hne : s.1.2 ≠ s.2.2)
    (hstart : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A := by
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  have hu0 := hstart (Q.u 0) (hmem 0).1 (Or.inl hports.1)
  have hv0 := hstart (Q.v 0) (hmem 0).2 (Or.inr hports.2.1)
  have hempty := block_empty_fullRungSequence M hM hA hC hcard Q hu0 hv0
  have hslot : s ∈ X.template.slots := by
    have hh : (s,k) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    exact (List.of_mem_zip hh).1
  have hs := template_slot_endpoints X s hslot
  have hN : X.template.n ≤ (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]
    omega
  have hlast := hlabels k hk le_rfl
  have he1 : Q.u k ≠ Q.v (k+1) := by
    intro he
    have hh := congrArg R.f he
    rw [hlast.1,hports.2.2.2] at hh
    omega
  have he2 : Q.v k ≠ Q.u (k+1) := by
    intro he
    have hh := congrArg R.f he
    rw [hlast.2,hports.2.2.1] at hh
    omega
  have hepair : Q.u (k+1) ≠ Q.v (k+1) := by
    intro he
    exact hne (hports.2.2.1.symm.trans ((congrArg R.f he).trans hports.2.2.2))
  obtain ⟨Rd⟩ := R.twoIncidences_of_edge_count (hmem (k+1)).1 (hmem (k+1)).2 (by
    rw [hports.2.2.1,hports.2.2.2]
    exact hdouble.trans (expand_core_double_count X R.k _ hdouble))
  have hend := block_empty_double_pair M hM hA hC hcard Rd hepair
    (hempty k hk le_rfl).1 (hempty k hk le_rfl).2 he1 he2
    (Mole.adj_symmetric M (Q.upper_next_adj k hk le_rfl))
    (Mole.adj_symmetric M (Q.lower_next_adj k hk le_rfl))
  intro v hv hlabel
  rcases hlabel with he | he
  · have hvu : v=Q.u (k+1) := R.injOn hv (hmem (k+1)).1 (he.trans hports.2.2.1.symm)
    simpa only [hvu] using hend.1
  · have hvv : v=Q.v (k+1) := R.injOn hv (hmem (k+1)).2 (he.trans hports.2.2.2.symm)
    simpa only [hvv] using hend.2

end WaveTurbulence.Vine
