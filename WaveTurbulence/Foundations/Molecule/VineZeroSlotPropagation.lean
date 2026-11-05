/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineZeroSlotEdges
public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineThinEmptyPairs
import Mathlib.Tactic

/-! # Propagation between core pairs across unexpanded slots -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A zero-rung slot propagates absence to a doubled terminal pair. -/
theorem block_zero_slot_double_end_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (hloc : X.template.slots.zip R.k=pre++(s,0)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.2,s.2.2)) (hne : s.1.2 ≠ s.2.2)
    (hstart : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A := by
  obtain ⟨Q,hmem,hports,_hlabels⟩ := R.has_rungSequence_ports pre post s 0 hloc
  have hslot : (s,0) ∈ X.template.slots.zip R.k := by
    rw [hloc]
    exact List.mem_append_right _ List.mem_cons_self
  have hcross := template_slot_cross_distinct X s (List.of_mem_zip hslot).1
  have hu0 := hstart (Q.u 0) (hmem 0).1 (Or.inl hports.1)
  have hv0 := hstart (Q.v 0) (hmem 0).2 (Or.inr hports.2.1)
  have hepair : Q.u 1 ≠ Q.v 1 := by
    intro he
    exact hne (hports.2.2.1.symm.trans ((congrArg R.f he).trans hports.2.2.2))
  have he1 : Q.u 0 ≠ Q.v 1 := by
    intro he
    exact hcross.1 (hports.1.symm.trans ((congrArg R.f he).trans hports.2.2.2))
  have he2 : Q.v 0 ≠ Q.u 1 := by
    intro he
    exact hcross.2 (hports.2.1.symm.trans ((congrArg R.f he).trans hports.2.2.1))
  obtain ⟨Rd⟩ := R.twoIncidences_of_edge_count (hmem 1).1 (hmem 1).2 (by
    rw [hports.2.2.1,hports.2.2.2]
    exact hdouble.trans (expand_core_double_count X R.k _ hdouble))
  have hend := block_empty_double_pair M hM hA hC hcard Rd hepair hu0 hv0 he1 he2
    (Mole.adj_symmetric M (R.zero_slot_adj s hslot s.1 (Or.inl rfl)
      (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1))
    (Mole.adj_symmetric M (R.zero_slot_adj s hslot s.2 (Or.inr rfl)
      (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2))
  intro v hv hlabel
  rcases hlabel with he | he
  · have hvu : v=Q.u 1 := R.injOn hv (hmem 1).1 (he.trans hports.2.2.1.symm)
    simpa only [hvu] using hend.1
  · have hvv : v=Q.v 1 := R.injOn hv (hmem 1).2 (he.trans hports.2.2.2.symm)
    simpa only [hvv] using hend.2

/-- A zero-rung slot propagates absence backwards to a doubled initial pair. -/
theorem block_zero_slot_double_start_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (hloc : X.template.slots.zip R.k=pre++(s,0)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.1,s.2.1)) (hne : s.1.1 ≠ s.2.1)
    (hend : ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A := by
  obtain ⟨Q,hmem,hports,_hlabels⟩ := R.has_rungSequence_ports pre post s 0 hloc
  have hslot : (s,0) ∈ X.template.slots.zip R.k := by
    rw [hloc]
    exact List.mem_append_right _ List.mem_cons_self
  have hcross := template_slot_cross_distinct X s (List.of_mem_zip hslot).1
  have hu1 := hend (Q.u 1) (hmem 1).1 (Or.inl hports.2.2.1)
  have hv1 := hend (Q.v 1) (hmem 1).2 (Or.inr hports.2.2.2)
  have hepair : Q.u 0 ≠ Q.v 0 := by
    intro he
    exact hne (hports.1.symm.trans ((congrArg R.f he).trans hports.2.1))
  have he1 : Q.u 1 ≠ Q.v 0 := by
    intro he
    exact hcross.2 (hports.2.1.symm.trans ((congrArg R.f he).symm.trans hports.2.2.1))
  have he2 : Q.v 1 ≠ Q.u 0 := by
    intro he
    exact hcross.1 (hports.1.symm.trans ((congrArg R.f he).symm.trans hports.2.2.2))
  obtain ⟨Rd⟩ := R.twoIncidences_of_edge_count (hmem 0).1 (hmem 0).2 (by
    rw [hports.1,hports.2.1]
    exact hdouble.trans (expand_core_double_count X R.k _ hdouble))
  have hstart := block_empty_double_pair M hM hA hC hcard Rd hepair hu1 hv1 he1 he2
    (R.zero_slot_adj s hslot s.1 (Or.inl rfl)
      (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1)
    (R.zero_slot_adj s hslot s.2 (Or.inr rfl)
      (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2)
  intro v hv hlabel
  rcases hlabel with he | he
  · have hvu : v=Q.u 0 := R.injOn hv (hmem 0).1 (he.trans hports.1.symm)
    simpa only [hvu] using hstart.1
  · have hvv : v=Q.v 0 := R.injOn hv (hmem 0).2 (he.trans hports.2.1.symm)
    simpa only [hvv] using hstart.2

end WaveTurbulence.Vine
