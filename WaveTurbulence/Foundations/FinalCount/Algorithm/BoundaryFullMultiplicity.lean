/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundaryStar
import Mathlib.Tactic

/-! # A full boundary multiplicity fixes every remaining neighbor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace BoundaryStar
variable {M : Molecule V D} {a b c : V} {k : ℕ}

theorem neighbor_eq_of_full_multiplicity (st : BoundaryStar M a b k) (hcb : c ≠ b)
    (hm : M.bondsBetween a c = k) (i : Fin k) : st.neighbor i = c := by
  classical
  have hsub : parallelBonds M a c ⊆ appbRemovedBonds M {a} \ parallelBonds M a b := by
    intro x hx
    refine mem_sdiff.mpr ⟨parallelBonds_subset_incident M a c hx,?_⟩
    intro hb
    have he := (mem_filter.mp hx).2.symm.trans (mem_filter.mp hb).2
    rcases Sym2.eq_iff.mp he with h | h
    · exact hcb h.2
    · exact hcb (h.2.trans h.1)
  have hcard : (appbRemovedBonds M {a} \ parallelBonds M a b).card = k := by
    have hh := Fintype.card_congr st.edge
    simpa only [Fintype.card_fin,Fintype.card_coe] using hh.symm
  have heq : parallelBonds M a c = appbRemovedBonds M {a} \ parallelBonds M a b := by
    apply eq_of_subset_of_card_le hsub
    rw [hcard]
    change k ≤ M.bondsBetween a c
    exact hm.ge
  have hx : (st.edge i).val ∈ parallelBonds M a c := by rw [heq]; exact (st.edge i).property
  have he := (st.endpoints i).symm.trans (mem_filter.mp hx).2
  rcases Sym2.eq_iff.mp he with h | h
  · exact h.2
  · exact h.2.trans h.1

end BoundaryStar
end WaveTurbulence.Mole.AppbAlgorithm
