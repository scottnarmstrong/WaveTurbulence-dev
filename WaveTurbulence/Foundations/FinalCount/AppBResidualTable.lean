/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSubrealization
import Mathlib.Tactic

/-! # Exact retained-bond tests for extracting residual atomic groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_endpoints_mem_vertices (i : Fin P.edges.length) :
    P.edges[i].1 ∈ P.vertices ∧ P.edges[i].2 ∈ P.vertices := by
  constructor
  all_goals
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩

theorem edge_survives_image_iff (Y : Finset ℕ) (hY : Y ⊆ P.vertices)
    (i : Fin P.edges.length) :
    (M.atom (r.edge i).val ∉ Y.image r.vertex ∧ M.atom (M.mate (r.edge i).val) ∉ Y.image r.vertex) ↔
      P.edges[i].1 ∉ Y ∧ P.edges[i].2 ∉ Y := by
  have hl := (edge_endpoints_mem_vertices (P := P) i).1
  have hr := (edge_endpoints_mem_vertices (P := P) i).2
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · rw [h.1,h.2,r.vertex_mem_image_iff Y hY _ hl,r.vertex_mem_image_iff Y hY _ hr]
  · rw [h.1,h.2,r.vertex_mem_image_iff Y hY _ hr,r.vertex_mem_image_iff Y hY _ hl,and_comm]

/-- An enumerated surviving old bond gives a literal retained dart. -/
@[expose] def retainedEdge (Y : Finset ℕ) (hY : Y ⊆ P.vertices) (i : Fin P.edges.length)
    (hi : P.edges[i].1 ∉ Y ∧ P.edges[i].2 ∉ Y) : Degen.RetainedDart M (Y.image r.vertex) :=
  ⟨(r.edge i).val,(r.edge_survives_image_iff Y hY i).mpr hi⟩

end AppbRealization
end WaveTurbulence.Mole
