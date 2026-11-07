/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostConnectivity
import Mathlib.Tactic

/-! # Every crossing has an actual surviving displayed endpoint -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem crossing_outer_displayed {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (x : D) (hx : M.atom x ∈ r.removedAtoms)
    (hy : M.atom (M.mate x) ∉ r.removedAtoms) :
    ∃ a ∈ P.vertices,a ∉ P.removed ∧ M.atom (M.mate x) = r.vertex a := by
  classical
  have hend : ∃ i : Fin P.edges.length,
      M.ends x = s(r.vertex P.edges[i].1,r.vertex P.edges[i].2) := by
    cases ho : M.out x
    · have hm : M.mate x ∈ appbRemovedBonds M r.removedAtoms := by
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,Or.inr ?_⟩
        · rw [M.out_mate,ho]; rfl
        · simpa only [M.mate_mate] using hx
      let i := r.edge.symm ⟨M.mate x,hm⟩
      have hi : (r.edge i).val = M.mate x := congrArg Subtype.val (r.edge.apply_symm_apply ⟨M.mate x,hm⟩)
      have he := r.endpoints i
      rw [hi] at he
      refine ⟨i,?_⟩
      have hs : M.ends x = M.ends (M.mate x) := by
        unfold Molecule.ends
        rw [M.mate_mate]
        exact Sym2.eq_swap
      exact hs.trans he
    · have hm : x ∈ appbRemovedBonds M r.removedAtoms :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,Or.inl hx⟩
      let i := r.edge.symm ⟨x,hm⟩
      have hi : (r.edge i).val = x := congrArg Subtype.val (r.edge.apply_symm_apply ⟨x,hm⟩)
      exact ⟨i,(by simpa only [hi] using r.endpoints i)⟩
  obtain ⟨i,hi⟩ := hend
  rcases Sym2.eq_iff.mp hi with he | he
  · refine ⟨P.edges[i].2,P.snd_mem_vertices i,?_,he.2⟩
    intro ha
    exact hy (he.2.symm ▸ mem_image_of_mem r.vertex ha)
  · refine ⟨P.edges[i].1,P.fst_mem_vertices i,?_,he.2⟩
    intro ha
    exact hy (he.2.symm ▸ mem_image_of_mem r.vertex ha)

end WaveTurbulence.Mole.AppbAlgorithm
