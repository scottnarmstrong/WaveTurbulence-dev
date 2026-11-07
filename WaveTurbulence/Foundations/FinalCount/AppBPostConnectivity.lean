/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalCuts
import Mathlib.Tactic

/-! # Reaching a displayed boundary atom in a residual component -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace AppbPattern

theorem fst_mem_vertices (P : AppbPattern) (i : Fin P.edges.length) : P.edges[i].1 ∈ P.vertices := by
  apply mem_union_right
  simp only [vertices,List.mem_toFinset,List.mem_flatMap]
  exact ⟨P.edges[i],List.getElem_mem _,by simp⟩

theorem snd_mem_vertices (P : AppbPattern) (i : Fin P.edges.length) : P.edges[i].2 ∈ P.vertices := by
  apply mem_union_right
  simp only [vertices,List.mem_toFinset,List.mem_flatMap]
  exact ⟨P.edges[i],List.getElem_mem _,by simp⟩

end AppbPattern
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Every actual residual component reaches a surviving displayed atom.
The witness is obtained from its nonempty old boundary, not assumed. -/
theorem post_reaches_displayed
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty) {v : V} (hv : v ∈ r.post.atoms) :
    ∃ a ∈ P.vertices, a ∉ P.removed ∧ r.post.SameComponent v (r.vertex a) := by
  classical
  have hcut := Degen.residual_boundary_nonempty_of_connected M hconn r.removedAtoms
    (hne.image r.vertex) r.removedAtoms_subset hv
  obtain ⟨x,hx⟩ := hcut
  have hxS := (mem_filter.mp hx).2.1
  have hremoved := Degen.residual_boundary_ends_in_removed M r.removedAtoms v hx
  have hr := (Degen.mem_residualComponent M r.removedAtoms v (M.atom x)).mp hxS
  have hp : r.post.SameComponent v (M.atom x) :=
    (Degen.eraseAtoms_sameComponent_iff M r.removedAtoms v (M.atom x)).mpr hr.2.2
  have hend : ∃ i : Fin P.edges.length,
      M.ends x = s(r.vertex P.edges[i].1,r.vertex P.edges[i].2) := by
    cases ho : M.out x
    · have hm : M.mate x ∈ appbRemovedBonds M r.removedAtoms := by
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
        · rw [M.out_mate,ho]; rfl
        · exact Or.inl hremoved
      let i := r.edge.symm ⟨M.mate x,hm⟩
      have hi : (r.edge i).val = M.mate x := congrArg Subtype.val (r.edge.apply_symm_apply ⟨M.mate x,hm⟩)
      have he := r.endpoints i
      rw [hi] at he
      refine ⟨i,?_⟩
      have hswap : M.ends x = M.ends (M.mate x) := by
        unfold Molecule.ends
        rw [M.mate_mate]
        exact Sym2.eq_swap
      exact hswap.trans he
    · have hm : x ∈ appbRemovedBonds M r.removedAtoms :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,Or.inr hremoved⟩
      let i := r.edge.symm ⟨x,hm⟩
      have hi : (r.edge i).val = x := congrArg Subtype.val (r.edge.apply_symm_apply ⟨x,hm⟩)
      refine ⟨i,?_⟩
      simpa only [hi] using r.endpoints i
  obtain ⟨i,he⟩ := hend
  unfold Molecule.ends at he
  rcases Sym2.eq_iff.mp he with h | h
  · refine ⟨P.edges[i].1,P.fst_mem_vertices i,?_,?_⟩
    · intro ha
      have hh : M.atom x ∈ r.removedAtoms := h.1.symm ▸ mem_image_of_mem r.vertex ha
      exact hr.2.1 hh
    · simpa only [h.1] using hp
  · refine ⟨P.edges[i].2,P.snd_mem_vertices i,?_,?_⟩
    · intro ha
      have hh : M.atom x ∈ r.removedAtoms := h.1.symm ▸ mem_image_of_mem r.vertex ha
      exact hr.2.1 hh
    · simpa only [h.1] using hp

/-- Connectivity of the finitely many surviving figure atoms gives the
full actual post connectivity, including all ambient vertices. -/
theorem post_connected_of_displayed
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty)
    (hlabels : ∀ a ∈ P.vertices, a ∉ P.removed → ∀ b ∈ P.vertices, b ∉ P.removed →
      r.post.SameComponent (r.vertex a) (r.vertex b)) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
  intro v hv w hw
  obtain ⟨a,ha,hka,hva⟩ := r.post_reaches_displayed hconn hne hv
  obtain ⟨b,hb,hkb,hwb⟩ := r.post_reaches_displayed hconn hne hw
  exact Relation.EqvGen.trans _ _ _ hva
    (Relation.EqvGen.trans _ _ _ (hlabels a ha hka b hb hkb) hwb.symm)

end AppbRealization
end WaveTurbulence.Mole
