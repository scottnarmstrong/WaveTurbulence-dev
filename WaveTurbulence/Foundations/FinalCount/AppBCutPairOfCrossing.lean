/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
import Mathlib.Tactic

/-! # Constructing a local cut pair from an exact ambient crossing set -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbCutPairOfCrossing {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (S : Finset V) (hS : S ⊆ M.atoms)
    (i j : Fin P.edges.length) (hne : i ≠ j)
    (hc : appbCrossingBonds M S = {(r.edge i).val,(r.edge j).val}) : AppbCutPair r S where
  subset_atoms := hS
  crossing := by
    intro x hx
    rw [hc] at hx
    rcases mem_insert.mp hx with h | h
    · exact h.symm ▸ (r.edge i).property
    · exact (mem_singleton.mp h).symm ▸ (r.edge j).property
  first := i
  second := j
  distinct := hne
  first_cross := by
    have h : (r.edge i).val ∈ appbCrossingBonds M S := hc.symm ▸ mem_insert_self _ _
    exact (mem_filter.mp h).2
  second_cross := by
    have h : (r.edge j).val ∈ appbCrossingBonds M S := hc.symm ▸ mem_insert_of_mem (mem_singleton_self _)
    exact (mem_filter.mp h).2
  other := by
    intro k hki hkj
    by_contra hn
    have hcross : (M.atom (r.edge k).val ∈ S ∧ M.atom (M.mate (r.edge k).val) ∉ S) ∨
        (M.atom (r.edge k).val ∉ S ∧ M.atom (M.mate (r.edge k).val) ∈ S) := by tauto
    have hx : (r.edge k).val ∈ appbCrossingBonds M S :=
      mem_filter.mpr ⟨(mem_filter.mp (r.edge k).property).1,hcross⟩
    rw [hc] at hx
    rcases mem_insert.mp hx with h | h
    · exact hki (r.edge.injective (Subtype.ext h))
    · exact hkj (r.edge.injective (Subtype.ext (mem_singleton.mp h)))

end WaveTurbulence.Mole
