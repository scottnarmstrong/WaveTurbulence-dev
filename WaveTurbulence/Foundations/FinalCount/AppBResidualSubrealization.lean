/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBResidualTable
import Mathlib.Tactic

/-! # Extracting a residual atomic group after deleting a listed subgroup -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem appb_mem_residual_removed (Y T : Finset V) (x : Degen.RetainedDart M Y) :
    x ∈ appbRemovedBonds (Degen.eraseAtoms M Y) T ↔
      M.out x.val = true ∧ (M.atom x.val ∈ T ∨ M.atom (M.mate x.val) ∈ T) := by
  constructor
  · intro hx
    obtain ⟨hb,ht⟩ := mem_filter.mp hx
    exact ⟨(mem_filter.mp hb).2,ht⟩
  · rintro ⟨ho,ht⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,ht⟩

noncomputable def residualSubrealization (Y : Finset ℕ) (hY : Y ⊆ P.vertices)
    (Q : AppbPattern) (hvertices : Q.vertices ⊆ P.vertices)
    (hremoved : Q.removed ⊆ P.removed) (hdisj : Disjoint Q.vertices Y)
    (e : Fin Q.edges.length ↪ Fin P.edges.length)
    (htable : ∀ j,P.edges[e j] = Q.edges[j])
    (hcover : ∀ i,(P.edges[i].1 ∉ Y ∧ P.edges[i].2 ∉ Y ∧
      (P.edges[i].1 ∈ Q.removed ∨ P.edges[i].2 ∈ Q.removed)) ↔ ∃ j,e j = i) :
    AppbRealization (Degen.eraseAtoms M (Y.image r.vertex)) Q := by
  classical
  let N := Degen.eraseAtoms M (Y.image r.vertex)
  have hQ : Q.removed ⊆ P.vertices := fun a ha => hvertices (mem_union_left _ ha)
  have hs (j : Fin Q.edges.length) : P.edges[e j].1 ∉ Y ∧ P.edges[e j].2 ∉ Y :=
    ((hcover (e j)).mpr ⟨j,rfl⟩).1 |> fun ha => ⟨ha,((hcover (e j)).mpr ⟨j,rfl⟩).2.1⟩
  let g : Fin Q.edges.length → {x // x ∈ appbRemovedBonds N (Q.removed.image r.vertex)} := fun j =>
    ⟨r.retainedEdge Y hY (e j) (hs j),(appb_mem_residual_removed (M := M) (Y.image r.vertex) (Q.removed.image r.vertex) _).mpr
      ⟨(mem_filter.mp (mem_filter.mp (r.edge (e j)).property).1).2,
        (mem_filter.mp ((r.edge_mem_removed_image_iff Q.removed hQ (e j)).mpr
          ((hcover (e j)).mpr ⟨j,rfl⟩).2.2)).2⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro j k he
      have hv := congrArg (fun x : {x // x ∈ appbRemovedBonds N (Q.removed.image r.vertex)} => x.val.val) he
      change (r.edge (e j)).val = (r.edge (e k)).val at hv
      exact e.injective (r.edge.injective (Subtype.ext hv))
    · intro x
      have hx := (appb_mem_residual_removed (M := M) (Y.image r.vertex) (Q.removed.image r.vertex) x.val).mp x.property
      have hold : x.val.val ∈ appbRemovedBonds M r.removedAtoms := by
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _,hx.1⟩,?_⟩
        have hh : Q.removed.image r.vertex ⊆ r.removedAtoms := image_subset_image hremoved
        exact hx.2.imp (fun h => hh h) (fun h => hh h)
      let i := r.edge.symm ⟨x.val.val,hold⟩
      have he : (r.edge i).val = x.val.val := congrArg Subtype.val (r.edge.apply_symm_apply ⟨x.val.val,hold⟩)
      have hkeep : P.edges[i].1 ∉ Y ∧ P.edges[i].2 ∉ Y :=
        (r.edge_survives_image_iff Y hY i).mp (he.symm ▸ x.val.property)
      have htouch : P.edges[i].1 ∈ Q.removed ∨ P.edges[i].2 ∈ Q.removed := by
        apply (r.edge_mem_removed_image_iff Q.removed hQ i).mp
        apply mem_filter.mpr
        exact ⟨mem_filter.mpr ⟨mem_univ _,he.symm ▸ hx.1⟩,he.symm ▸ hx.2⟩
      obtain ⟨j,hj⟩ := (hcover i).mp ⟨hkeep.1,hkeep.2,htouch⟩
      refine ⟨j,Subtype.ext (Subtype.ext ?_)⟩
      change (r.edge (e j)).val = x.val.val
      rw [hj,he]
  exact {
    vertex := r.vertex
    vertex_injective := r.vertex_injective.mono hvertices
    vertex_mem := fun a ha => mem_sdiff.mpr ⟨r.vertex_mem a (hvertices ha),fun hy =>
      disjoint_left.mp hdisj ha ((r.vertex_mem_image_iff Y hY a (hvertices ha)).mp hy)⟩
    edge := Equiv.ofBijective g hg
    endpoints := fun j => by
      change M.ends (r.edge (e j)).val = _
      rw [r.endpoints,htable]
  }

end AppbRealization
end WaveTurbulence.Mole
