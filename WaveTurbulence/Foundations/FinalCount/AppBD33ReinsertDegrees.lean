/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # Exact survivor degrees and V3 effect of double-pair reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_reinsert_degree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) {v : V} (hv : v ∉ r.removedAtoms) :
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).deg v = M.deg v := by
  have h3 := r.post_vertex_degree 3 (by decide)
  have h4 := r.post_vertex_degree 4 (by decide)
  have h3deg : r.post.deg (r.vertex 3)+1 = M.deg (r.vertex 3) := h3
  have h4deg : r.post.deg (r.vertex 4)+1 = M.deg (r.vertex 4) := h4
  have h34 : r.vertex 3 ≠ r.vertex 4 := by
    intro he
    have hh := r.vertex_injective (by decide : 3 ∈ AppbPatternKind.d33.pattern.vertices)
      (by decide : 4 ∈ AppbPatternKind.d33.pattern.vertices) he
    omega
  have hpost : r.post.deg v+(if r.vertex 3 = v then 1 else 0)+(if r.vertex 4 = v then 1 else 0) = M.deg v := by
    by_cases hA : r.vertex 3 = v
    · subst v
      simpa only [ite_true,h34.symm,ite_false,add_zero] using h3deg
    by_cases hB : r.vertex 4 = v
    · subst v
      simpa only [h34,ite_false,zero_add,ite_true] using h4deg
    have hout : v ∉ AppbPatternKind.d33.pattern.vertices.image r.vertex := by
      intro hh
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hh
      have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
        simp only [AppbPatternKind.pattern,AppbPattern.vertices] at ha
        simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_flatMap] at ha
        grind
      rcases ha' with rfl | rfl | rfl | rfl
      · exact hv (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.d33.pattern.removed by decide))
      · exact hv (mem_image_of_mem _ (show 2 ∈ AppbPatternKind.d33.pattern.removed by decide))
      · exact hA rfl
      · exact hB rfl
    simp only [hA,hB,ite_false,add_zero,r.post_degree_outside _ hout]
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · exact (r.postWithBond_degree 3 4 v).trans hpost
  · rw [r.postWithBond_degree]
    omega

end WaveTurbulence.Mole
