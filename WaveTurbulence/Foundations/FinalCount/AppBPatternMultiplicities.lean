/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalMultiplicity
import Mathlib.Tactic

/-! # Actual neighbour multiplicities reflected into the finite figure table -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def AppbPattern.multiplicity (P : AppbPattern) (a b : ℕ) : ℕ :=
  ∑ i : Fin P.edges.length,if s(P.edges[i].1,P.edges[i].2) = s(a,b) then 1 else 0

theorem AppbPattern.edge_fst_mem (P : AppbPattern) (i : Fin P.edges.length) : P.edges[i].1 ∈ P.vertices := by
  apply mem_union_right
  simp only [List.mem_toFinset,List.mem_flatMap]
  exact ⟨P.edges[i],List.getElem_mem _,by simp⟩

theorem AppbPattern.edge_snd_mem (P : AppbPattern) (i : Fin P.edges.length) : P.edges[i].2 ∈ P.vertices := by
  apply mem_union_right
  simp only [List.mem_toFinset,List.mem_flatMap]
  exact ⟨P.edges[i],List.getElem_mem _,by simp⟩

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem edge_ends_eq_iff (i : Fin P.edges.length) (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) :
    M.ends (r.edge i).val = s(r.vertex a,r.vertex b) ↔ s(P.edges[i].1,P.edges[i].2) = s(a,b) := by
  rw [r.endpoints,Sym2.eq_iff,Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨r.vertex_injective (P.edge_fst_mem i) ha h.1,r.vertex_injective (P.edge_snd_mem i) hb h.2⟩
    · exact Or.inr ⟨r.vertex_injective (P.edge_fst_mem i) hb h.1,r.vertex_injective (P.edge_snd_mem i) ha h.2⟩
  · rintro (h | h)
    · exact Or.inl ⟨congrArg r.vertex h.1,congrArg r.vertex h.2⟩
    · exact Or.inr ⟨congrArg r.vertex h.1,congrArg r.vertex h.2⟩

theorem bondsBetween_vertices_eq (a b : ℕ) (ha : a ∈ P.removed) (hb : b ∈ P.vertices) :
    M.bondsBetween (r.vertex a) (r.vertex b) = P.multiplicity a b := by
  rw [r.bondsBetween_eq_local_sum (mem_image_of_mem _ ha)]
  unfold AppbPattern.multiplicity
  apply sum_congr rfl
  intro i hi
  simp only [r.edge_ends_eq_iff i a b (mem_union_left _ ha) hb]

/-- Every actual neighbour of a deleted atom occurs among the displayed
vertices, since every incident bond is enumerated by the realization. -/
theorem neighbor_mem_vertices (a : ℕ) (ha : a ∈ P.removed) {b : V}
    (hpos : 0 < M.bondsBetween (r.vertex a) b) : ∃ c ∈ P.vertices,b = r.vertex c := by
  obtain ⟨x,hx⟩ := card_pos.mp hpos
  obtain ⟨hxout,hxe⟩ := mem_filter.mp hx
  have hrem : x ∈ appbRemovedBonds M r.removedAtoms := by
    apply mem_filter.mpr
    refine ⟨hxout,?_⟩
    rcases Sym2.eq_iff.mp hxe with h | h
    · exact Or.inl (h.1.symm ▸ mem_image_of_mem r.vertex ha)
    · exact Or.inr (h.2.symm ▸ mem_image_of_mem r.vertex ha)
  let i := r.edge.symm ⟨x,hrem⟩
  have hi : (r.edge i).val = x := congrArg Subtype.val (r.edge.apply_symm_apply _)
  have he := r.endpoints i
  rw [hi] at he
  have hh := hxe.symm.trans he
  rcases Sym2.eq_iff.mp hh with h | h
  · exact ⟨P.edges[i].2,P.edge_snd_mem i,h.2⟩
  · exact ⟨P.edges[i].1,P.edge_fst_mem i,h.2⟩

end AppbRealization
end WaveTurbulence.Mole
