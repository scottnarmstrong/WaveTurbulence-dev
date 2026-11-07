/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialEndpointExclusion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewSpecialDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # Normal double-pair steps cannot create special bonds along regular rails -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace D33Special
variable {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern)

theorem displayed_survivor {b : V} (hb : b ∈ r.post.atoms)
    (hi : b ∈ AppbPatternKind.d33.pattern.vertices.image r.vertex) :
    b = r.vertex 3 ∨ b = r.vertex 4 := by
  obtain ⟨j,hj,hj'⟩ := mem_image.mp hi
  have hV : AppbPatternKind.d33.pattern.vertices = {1,2,3,4} := by decide
  rw [hV] at hj
  simp only [mem_insert,mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · exact ((mem_sdiff.mp hb).2 (hj' ▸ mem_image_of_mem r.vertex (by decide : 1 ∈ AppbPatternKind.d33.pattern.removed))).elim
  · exact ((mem_sdiff.mp hb).2 (hj' ▸ mem_image_of_mem r.vertex (by decide : 2 ∈ AppbPatternKind.d33.pattern.removed))).elim
  · exact Or.inl hj'.symm
  · exact Or.inr hj'.symm

theorem no_new_special (hno : AppbNoLoops M)
    (hdouble : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2)
    (hn : ∀ b ∈ M.atoms,b ∉ AppbPatternKind.d33.pattern.vertices.image r.vertex →
      (M.bondsBetween (r.vertex 3) b = 1 ∨ M.bondsBetween (r.vertex 4) b = 1) → M.deg b ≠ 3)
    (x : Degen.RetainedDart M r.removedAtoms) (hs : AppbSpecial r.post x) : AppbSpecial M x.val := by
  have hno' : AppbNoLoops r.post := fun x => hno x.val
  have h3not : r.vertex 3 ∉ r.removedAtoms := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have h4not : r.vertex 4 ∉ r.removedAtoms := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hn3 : ∀ b ∈ r.post.atoms,r.vertex 3 ≠ b → r.post.bondsBetween (r.vertex 3) b = 1 → r.post.deg b ≠ 3 := by
    intro b hb hne hm
    have hm' : M.bondsBetween (r.vertex 3) b = 1 :=
      (Degen.bondsBetween_erase_eq M r.removedAtoms h3not (mem_sdiff.mp hb).2).symm.trans hm
    by_cases hi : b ∈ AppbPatternKind.d33.pattern.vertices.image r.vertex
    · rcases displayed_survivor r hb hi with he | he
      · exact (hne he.symm).elim
      · rw [he,hdouble] at hm'
        omega
    · rw [r.post_degree_outside b hi]
      exact hn b (mem_sdiff.mp hb).1 hi (Or.inl hm')
  have hn4 : ∀ b ∈ r.post.atoms,r.vertex 4 ≠ b → r.post.bondsBetween (r.vertex 4) b = 1 → r.post.deg b ≠ 3 := by
    intro b hb hne hm
    have hm' : M.bondsBetween (r.vertex 4) b = 1 :=
      (Degen.bondsBetween_erase_eq M r.removedAtoms h4not (mem_sdiff.mp hb).2).symm.trans hm
    by_cases hi : b ∈ AppbPatternKind.d33.pattern.vertices.image r.vertex
    · rcases displayed_survivor r hb hi with he | he
      · rw [he,bondsBetween_symm M (r.vertex 4) (r.vertex 3),hdouble] at hm'
        omega
      · exact (hne he.symm).elim
    · rw [r.post_degree_outside b hi]
      exact hn b (mem_sdiff.mp hb).1 hi (Or.inr hm')
  have hx3 := special_endpoints_ne_of_no_three_single_neighbor r.post hno' hn3 hs
  have hx4 := special_endpoints_ne_of_no_three_single_neighbor r.post hno' hn4 hs
  have hsrc : M.atom x.val ∉ AppbPatternKind.d33.pattern.vertices.image r.vertex := by
    intro hi
    rcases displayed_survivor r (r.post.atom_mem x) hi with he | he
    · exact hx3.1 he
    · exact hx4.1 he
  have htgt : M.atom (M.mate x.val) ∉ AppbPatternKind.d33.pattern.vertices.image r.vertex := by
    intro hi
    rcases displayed_survivor r (r.post.atom_mem (r.post.mate x)) hi with he | he
    · exact hx3.2 he
    · exact hx4.2 he
  exact SpecialDeletion.old_of_endpoints_outside r x hsrc htgt hs

end D33Special
end WaveTurbulence.Mole.AppbAlgorithm
