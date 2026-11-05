/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotDoubleEnd
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungsReverse
import Mathlib.Tactic

/-! # Empty terminal slot endpoints force the doubled initial pair absent -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reverse propagation through a positive-length slot and its old doubled
initial pair, using only actual doubled darts and rail edges. -/
theorem block_slot_double_start_absent (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (hk : 1 ≤ k)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hdouble : 2 ≤ X.template.bonds.count (s.1.1,s.2.1)) (hne : s.1.1 ≠ s.2.1)
    (hend : ∀ v ∈ S,R.f v=s.1.2 ∨ R.f v=s.2.2 → v ∉ A) :
    ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A := by
  obtain ⟨Q,hmem,hports,hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  have huN := hend (Q.u (k+1)) (hmem (k+1)).1 (Or.inl hports.2.2.1)
  have hvN := hend (Q.v (k+1)) (hmem (k+1)).2 (Or.inr hports.2.2.2)
  have hempty := block_empty_fullRungSequence_reverse M hM hA hC hcard Q huN hvN
  have hslot : s ∈ X.template.slots := by
    have hh : (s,k) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    exact (List.of_mem_zip hh).1
  have hs := template_slot_endpoints X s hslot
  have hN : X.template.n ≤ (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]
    omega
  have hfirst := hlabels 1 le_rfl hk
  have he1 : Q.u 1 ≠ Q.v 0 := by
    intro he
    have hh := congrArg R.f he
    rw [hfirst.1,hports.2.1] at hh
    omega
  have he2 : Q.v 1 ≠ Q.u 0 := by
    intro he
    have hh := congrArg R.f he
    rw [hfirst.2,hports.1] at hh
    omega
  have hepair : Q.u 0 ≠ Q.v 0 := by
    intro he
    exact hne (hports.1.symm.trans ((congrArg R.f he).trans hports.2.1))
  obtain ⟨Rd⟩ := R.twoIncidences_of_edge_count (hmem 0).1 (hmem 0).2 (by
    rw [hports.1,hports.2.1]
    exact hdouble.trans (expand_core_double_count X R.k _ hdouble))
  have hstart := block_empty_double_pair M hM hA hC hcard Rd hepair
    (hempty 1 le_rfl hk).1 (hempty 1 le_rfl hk).2 he1 he2
    (Mole.adj_symmetric M (Q.upper_prev_adj 1 le_rfl hk))
    (Mole.adj_symmetric M (Q.lower_prev_adj 1 le_rfl hk))
  intro v hv hlabel
  rcases hlabel with he | he
  · have hvu : v=Q.u 0 := R.injOn hv (hmem 0).1 (he.trans hports.1.symm)
    simpa only [hvu] using hstart.1
  · have hvv : v=Q.v 0 := R.injOn hv (hmem 0).2 (he.trans hports.2.1.symm)
    simpa only [hvv] using hstart.2

end WaveTurbulence.Vine
