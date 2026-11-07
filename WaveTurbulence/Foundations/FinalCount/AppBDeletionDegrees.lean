/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
import Mathlib.Tactic

/-! # Exact survivor degrees from Appendix B incidence lists -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reindex a bond sum by the actual retained outgoing representatives. -/
theorem appb_sum_bonds_eraseAtoms (M : Molecule V D) (Y : Finset V)
    {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ x ∈ (Degen.eraseAtoms M Y).bonds, f x.val) =
      ∑ x ∈ M.bonds.filter (fun x => M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y), f x := by
  apply sum_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,x.property⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨hx,hp⟩ := mem_filter.mp hx
    exact ⟨⟨x,hp⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,rfl⟩
  · intro x _; rfl

/-- Exact decomposition of degree into retained and removed bond incidences.
It includes removed vertices and loops, without any degree cap. -/
theorem appb_degree_partition (M : Molecule V D) (Y : Finset V) (v : V) :
    (Degen.eraseAtoms M Y).deg v +
      (∑ x ∈ appbRemovedBonds M Y, appbIncidence M v x) = M.deg v := by
  rw [appb_degree_bond_sum (Degen.eraseAtoms M Y),appb_degree_bond_sum M]
  change (∑ x ∈ (Degen.eraseAtoms M Y).bonds, appbIncidence M v x.val) + _ = _
  rw [appb_sum_bonds_eraseAtoms]
  have he : M.bonds.filter (fun x => M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y) =
      M.bonds.filter (fun x => ¬(M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y)) := by
    ext x
    simp only [mem_filter,not_or]
  rw [he,appbRemovedBonds,add_comm]
  exact sum_filter_add_sum_filter_not _ _ _

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Exact degree decrement at each labeled vertex, including survivors.
Boundary degrees in the ambient molecule are not silently prescribed. -/
theorem post_vertex_degree (a : ℕ) (ha : a ∈ P.vertices) :
    r.post.deg (r.vertex a) + P.localDegree a = M.deg (r.vertex a) := by
  have hh := appb_degree_partition M r.removedAtoms (r.vertex a)
  rw [← r.removedBond_sum] at hh
  have he : (∑ i : Fin P.edges.length, appbIncidence M (r.vertex a) (r.edge i).val) =
      P.localDegree a := by
    unfold AppbPattern.localDegree
    apply sum_congr rfl
    intro i _
    exact r.edge_incidence i a ha
  rw [he] at hh
  exact hh

/-- Unlabeled ambient vertices have no incident bond in the deletion list,
and hence keep their degree exactly. -/
theorem post_degree_outside (v : V) (hv : v ∉ P.vertices.image r.vertex) : r.post.deg v = M.deg v := by
  have hh := appb_degree_partition M r.removedAtoms v
  rw [← r.removedBond_sum] at hh
  have hz : (∑ i : Fin P.edges.length, appbIncidence M v (r.edge i).val) = 0 := by
    apply sum_eq_zero
    intro i _
    have hl : r.vertex P.edges[i].1 ≠ v := by
      intro he
      apply hv
      apply mem_image.mpr
      refine ⟨P.edges[i].1,mem_union_right _ ?_,he⟩
      simp only [List.mem_toFinset,List.mem_flatMap]
      exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
    have hr : r.vertex P.edges[i].2 ≠ v := by
      intro he
      apply hv
      apply mem_image.mpr
      refine ⟨P.edges[i].2,mem_union_right _ ?_,he⟩
      simp only [List.mem_toFinset,List.mem_flatMap]
      exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
    have hs := r.endpoints i
    unfold Molecule.ends at hs
    rcases Sym2.eq_iff.mp hs with h | h
    · simp only [appbIncidence,h.1,h.2,hl,hr,ite_false,zero_add]
    · simp only [appbIncidence,h.1,h.2,hl,hr,ite_false,zero_add]
  rw [hz,add_zero] at hh
  exact hh

end AppbRealization
end WaveTurbulence.Mole
