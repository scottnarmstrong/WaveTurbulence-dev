/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
import Mathlib.Tactic

/-! # Extracting an actual atomic subgroup from a figure table -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
private theorem mem_removed_bonds (M : Molecule V D) (Y : Finset V) (x : D) :
    x ∈ appbRemovedBonds M Y ↔ x ∈ M.bonds ∧
      (M.atom x ∈ Y ∨ M.atom (M.mate x) ∈ Y) := by
  simp only [appbRemovedBonds,mem_filter]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem vertex_mem_image_iff (T : Finset ℕ) (hT : T ⊆ P.vertices)
    (a : ℕ) (ha : a ∈ P.vertices) : r.vertex a ∈ T.image r.vertex ↔ a ∈ T := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := mem_image.mp h
    exact (r.vertex_injective (hT hb) ha he) ▸ hb
  · exact mem_image_of_mem _

theorem edge_mem_removed_image_iff (T : Finset ℕ) (hT : T ⊆ P.vertices)
    (i : Fin P.edges.length) :
    (r.edge i).val ∈ appbRemovedBonds M (T.image r.vertex) ↔
      P.edges[i].1 ∈ T ∨ P.edges[i].2 ∈ T := by
  have hl : P.edges[i].1 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hr : P.edges[i].2 ∈ P.vertices := by
    apply mem_union_right
    simp only [List.mem_toFinset,List.mem_flatMap]
    exact ⟨P.edges[i],List.getElem_mem _,by simp⟩
  have hb := (mem_filter.mp (r.edge i).property).1
  rw [mem_removed_bonds,and_iff_right hb]
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · rw [h.1,h.2,r.vertex_mem_image_iff T hT _ hl,r.vertex_mem_image_iff T hT _ hr]
  · rw [h.1,h.2,r.vertex_mem_image_iff T hT _ hr,r.vertex_mem_image_iff T hT _ hl,or_comm]

/-- Every field supplied here is a finite input-table fact. The outgoing
bond equivalence of the subgroup is constructed from the actual graph. -/
noncomputable def subrealization (Q : AppbPattern)
    (hvertices : Q.vertices ⊆ P.vertices) (hremoved : Q.removed ⊆ P.removed)
    (e : Fin Q.edges.length ↪ Fin P.edges.length)
    (htable : ∀ j,P.edges[e j] = Q.edges[j])
    (hcover : ∀ i,(P.edges[i].1 ∈ Q.removed ∨ P.edges[i].2 ∈ Q.removed) ↔ ∃ j,e j = i) :
    AppbRealization M Q := by
  classical
  have hQ : Q.removed ⊆ P.vertices := fun a ha => hvertices (mem_union_left _ ha)
  let g : Fin Q.edges.length → {x // x ∈ appbRemovedBonds M (Q.removed.image r.vertex)} :=
    fun j => ⟨(r.edge (e j)).val,(r.edge_mem_removed_image_iff Q.removed hQ (e j)).mpr
      ((hcover (e j)).mpr ⟨j,rfl⟩)⟩
  have hg : Function.Bijective g := by
    constructor
    · intro j k he
      have hv := congrArg (fun x : {x // x ∈ appbRemovedBonds M (Q.removed.image r.vertex)} => x.val) he
      change (r.edge (e j)).val = (r.edge (e k)).val at hv
      exact e.injective (r.edge.injective (Subtype.ext hv))
    · intro x
      have hx : x.val ∈ appbRemovedBonds M r.removedAtoms := by
        obtain ⟨hb,ht⟩ := mem_filter.mp x.property
        apply mem_filter.mpr
        refine ⟨hb,?_⟩
        have hs : Q.removed.image r.vertex ⊆ r.removedAtoms := image_subset_image hremoved
        exact ht.imp (fun h => hs h) (fun h => hs h)
      let i := r.edge.symm ⟨x.val,hx⟩
      have he : (r.edge i).val = x.val := congrArg Subtype.val (r.edge.apply_symm_apply ⟨x.val,hx⟩)
      have hm : (r.edge i).val ∈ appbRemovedBonds M (Q.removed.image r.vertex) := he.symm ▸ x.property
      obtain ⟨j,hj⟩ := (hcover i).mp ((r.edge_mem_removed_image_iff Q.removed hQ i).mp hm)
      refine ⟨j,Subtype.ext ?_⟩
      change (r.edge (e j)).val = x.val
      rw [hj,he]
  exact {
    vertex := r.vertex
    vertex_injective := r.vertex_injective.mono hvertices
    vertex_mem := fun a ha => r.vertex_mem a (hvertices ha)
    edge := Equiv.ofBijective g hg
    endpoints := fun j => by
      change M.ends (r.edge (e j)).val = _
      rw [r.endpoints,htable]
  }

end AppbRealization
end WaveTurbulence.Mole
