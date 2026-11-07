/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Cut-side tests transported from unordered figure endpoint pairs -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_cut_cross_iff (S : Finset V) (i : Fin P.edges.length) :
    ((M.atom (r.edge i).val ∈ S ∧ M.atom (M.mate (r.edge i).val) ∉ S) ∨
      (M.atom (r.edge i).val ∉ S ∧ M.atom (M.mate (r.edge i).val) ∈ S)) ↔
    ((r.vertex P.edges[i].1 ∈ S ∧ r.vertex P.edges[i].2 ∉ S) ∨
      (r.vertex P.edges[i].1 ∉ S ∧ r.vertex P.edges[i].2 ∈ S)) := by
  have he := r.endpoints i
  rcases Sym2.eq_iff.mp he with h | h
  · simp only [h.1,h.2]
  · simp only [h.1,h.2]
    tauto

theorem edge_cut_same_iff (S : Finset V) (i : Fin P.edges.length) :
    (M.atom (r.edge i).val ∈ S ↔ M.atom (M.mate (r.edge i).val) ∈ S) ↔
      (r.vertex P.edges[i].1 ∈ S ↔ r.vertex P.edges[i].2 ∈ S) := by
  have he := r.endpoints i
  rcases Sym2.eq_iff.mp he with h | h
  · simp only [h.1,h.2]
  · simp only [h.1,h.2]
    tauto

end AppbRealization
end WaveTurbulence.Mole
