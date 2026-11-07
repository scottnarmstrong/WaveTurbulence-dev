/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SharedCut
import Mathlib.Tactic

/-! # Complete residual topology alternatives for the first two 3S3New figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_shared_connected_of_common (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ appbS33SharedKinds) (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (h34 : r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
    ∀ u ∈ r.post.atoms,∀ v ∈ r.post.atoms,r.post.SameComponent u v := by
  simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl
  · exact appb_s33new1_connected_of_common_connected M r hconn hbridge h34
  · apply r.post_connected_of_boundary_representative 3 hconn (by decide)
    intro a ha hka
    have hset : AppbPatternKind.s33new2.pattern.vertices = {1,2,3,4} := by decide
    rw [hset] at ha
    simp only [mem_insert,mem_singleton] at ha
    have hh : a ≠ 1 ∧ a ≠ 2 := by simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton,not_or] using hka
    rcases ha with rfl | rfl | rfl | rfl
    · exact False.elim (hh.1 rfl)
    · exact False.elim (hh.2 rfl)
    · exact Relation.EqvGen.refl _
    · exact h34

theorem appb_s33_shared_side_of_not_connected (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ appbS33SharedKinds) (r : AppbRealization M k.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (h34 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
    ∀ a ∈ k.pattern.vertices,r.vertex a ∈ Degen.residualComponent M r.removedAtoms (r.vertex 3) ↔ a = 3 := by
  simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl
  · exact appb_s33new1_common_side_labels M r hbridge h34
  · intro a ha
    have hset : AppbPatternKind.s33new2.pattern.vertices = {1,2,3,4} := by decide
    rw [hset] at ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · simp only [r.removed_vertex_not_in_residual 3 1 (by decide),false_iff]; decide
    · simp only [r.removed_vertex_not_in_residual 3 2 (by decide),false_iff]; decide
    · rw [r.residual_vertex_mem_iff 3 3 (by decide) (by decide)]; exact ⟨fun _ => rfl,fun _ => Relation.EqvGen.refl _⟩
    · rw [r.residual_vertex_mem_iff 3 4 (by decide) (by decide)]; simp only [h34,false_iff]; decide

end WaveTurbulence.Mole
