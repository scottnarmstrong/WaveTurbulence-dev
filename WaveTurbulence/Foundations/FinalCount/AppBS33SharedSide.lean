/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
public import WaveTurbulence.Foundations.FinalCount.AppBLocalCuts
import Mathlib.Tactic

/-! # The common-neighbour residual side in the first two 3S3New figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The lone fifth boundary label cannot form its own old one-bond cut. -/
theorem appb_s33new1_fifth_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new1.pattern) (hbridge : ∀ e : D,¬Degen.IsBridge M e) :
    r.post.SameComponent (r.vertex 3) (r.vertex 5) ∨ r.post.SameComponent (r.vertex 4) (r.vertex 5) := by
  classical
  by_contra hn
  push Not at hn
  let S := Degen.residualComponent M r.removedAtoms (r.vertex 5)
  have hmem (a : ℕ) (ha : a ∈ AppbPatternKind.s33new1.pattern.vertices) (hk : a ∉ AppbPatternKind.s33new1.pattern.removed) :
      r.vertex a ∈ S ↔ r.post.SameComponent (r.vertex 5) (r.vertex a) := r.residual_vertex_mem_iff 5 a ha hk
  have h1 := r.removed_vertex_not_in_residual 5 1 (by decide)
  have h2 := r.removed_vertex_not_in_residual 5 2 (by decide)
  change r.vertex 1 ∉ S at h1
  change r.vertex 2 ∉ S at h2
  have h3 : r.vertex 3 ∉ S := fun h => hn.1 ((hmem 3 (by decide) (by decide)).mp h).symm
  have h4 : r.vertex 4 ∉ S := fun h => hn.2 ((hmem 4 (by decide) (by decide)).mp h).symm
  have h5 : r.vertex 5 ∈ S := (hmem 5 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  apply r.cutCount_ne_one S (r.residual_cut_crossing (r.vertex 5)) hbridge
  change (∑ i : Fin 5,if
    (r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].1) ∈ S ∧
      r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].2) ∉ S) ∨
    (r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].1) ∉ S ∧
      r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].2) ∈ S) then 1 else 0) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num [h1,h2,h3,h4,h5]

/-- If common neighbour 3 and neighbour 4 are connected, every surviving
figure label belongs to that component. -/
theorem appb_s33new1_connected_of_common_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new1.pattern)
    (hconn : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (h34 : r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
    ∀ u ∈ r.post.atoms,∀ v ∈ r.post.atoms,r.post.SameComponent u v := by
  have h35 : r.post.SameComponent (r.vertex 3) (r.vertex 5) := by
    rcases appb_s33new1_fifth_connected M r hbridge with h | h
    · exact h
    · exact Relation.EqvGen.trans _ _ _ h34 h
  apply r.post_connected_of_boundary_representative 3 hconn (by decide)
  intro a ha hka
  have hset : AppbPatternKind.s33new1.pattern.vertices = {1,2,3,4,5} := by decide
  rw [hset] at ha
  simp only [mem_insert,mem_singleton] at ha
  have hk : a ≠ 1 ∧ a ≠ 2 := by simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton,not_or] using hka
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hk.1 rfl)
  · exact False.elim (hk.2 rfl)
  · exact Relation.EqvGen.refl _
  · exact h34
  · exact h35

/-- In a split residual graph, the common neighbour has no other displayed
surviving label on its side, by the two forbidden one-bond cuts. -/
theorem appb_s33new1_common_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new1.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) (h34 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
    ∀ a ∈ AppbPatternKind.s33new1.pattern.vertices,
      r.vertex a ∈ Degen.residualComponent M r.removedAtoms (r.vertex 3) ↔ a = 3 := by
  classical
  have h35 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 5) := by
    intro hh
    let S := Degen.residualComponent M r.removedAtoms (r.vertex 4)
    have hmem (a : ℕ) (ha : a ∈ AppbPatternKind.s33new1.pattern.vertices) (hk : a ∉ AppbPatternKind.s33new1.pattern.removed) :
        r.vertex a ∈ S ↔ r.post.SameComponent (r.vertex 4) (r.vertex a) := r.residual_vertex_mem_iff 4 a ha hk
    have h1 := r.removed_vertex_not_in_residual 4 1 (by decide)
    have h2 := r.removed_vertex_not_in_residual 4 2 (by decide)
    change r.vertex 1 ∉ S at h1
    change r.vertex 2 ∉ S at h2
    have h3 : r.vertex 3 ∉ S := fun h => h34 ((hmem 3 (by decide) (by decide)).mp h).symm
    have h4 : r.vertex 4 ∈ S := (hmem 4 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
    have h5 : r.vertex 5 ∉ S := by
      intro h
      exact h34 (Relation.EqvGen.trans _ _ _ hh ((hmem 5 (by decide) (by decide)).mp h).symm)
    apply r.cutCount_ne_one S (r.residual_cut_crossing (r.vertex 4)) hbridge
    change (∑ i : Fin 5,if
      (r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].1) ∈ S ∧
        r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].2) ∉ S) ∨
      (r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].1) ∉ S ∧
        r.vertex ([(1,2),(1,3),(1,4),(2,3),(2,5)][i].2) ∈ S) then 1 else 0) = 1
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    norm_num [h1,h2,h3,h4,h5]
  intro a ha
  have hset : AppbPatternKind.s33new1.pattern.vertices = {1,2,3,4,5} := by decide
  rw [hset] at ha
  simp only [mem_insert,mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simp only [r.removed_vertex_not_in_residual 3 1 (by decide),false_iff]; decide
  · simp only [r.removed_vertex_not_in_residual 3 2 (by decide),false_iff]; decide
  · rw [r.residual_vertex_mem_iff 3 3 (by decide) (by decide)]; exact ⟨fun _ => rfl,fun _ => Relation.EqvGen.refl _⟩
  · rw [r.residual_vertex_mem_iff 3 4 (by decide) (by decide)]; simp only [h34,false_iff]; decide
  · rw [r.residual_vertex_mem_iff 3 5 (by decide) (by decide)]; simp only [h35,false_iff]; decide

end WaveTurbulence.Mole
