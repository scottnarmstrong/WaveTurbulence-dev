/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33RuleSelection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PatternReachability
import Mathlib.Tactic

/-! # Old degree-four boundary facts are derived from the source ladder tests -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_boundary_four_of_post_three {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : r.post.deg (r.vertex 3) = 3) (h4 : r.post.deg (r.vertex 4) = 3) :
    M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4 := by
  have he3 := r.post_vertex_degree 3 (by decide)
  have he4 := r.post_vertex_degree 4 (by decide)
  have hn3 : AppbPatternKind.d33.pattern.localDegree 3 = 1 := by decide
  have hn4 : AppbPatternKind.d33.pattern.localDegree 4 = 1 := by decide
  rw [hn3,h3] at he3
  rw [hn4,h4] at he4
  exact ⟨he3.symm,he4.symm⟩

theorem D33Continues.boundary_four {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : D33Continues r) :
    M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4 := by
  obtain ⟨t,ht,ho⟩ := h
  have h1 : r.post.deg (t.vertex 1) = 3 := (t.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : r.post.deg (t.vertex 2) = 3 := (t.deleted_degree 2 (by decide)).trans (by decide)
  rcases ht with ⟨ht1,ht2⟩ | ⟨ht1,ht2⟩
  · rw [ht1] at h1
    rw [ht2] at h2
    exact d33_boundary_four_of_post_three r h1 h2
  · rw [ht1] at h1
    rw [ht2] at h2
    exact d33_boundary_four_of_post_three r h2 h1

theorem HasD33ResidualCommon.boundary_four {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : HasD33ResidualCommon r) :
    M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4 := by
  obtain ⟨t,ht⟩ := h
  have h1 : r.post.deg (t.vertex 1) = 3 := (t.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : r.post.deg (t.vertex 2) = 3 := (t.deleted_degree 2 (by decide)).trans (by decide)
  rcases ht with ⟨ht1,ht2⟩ | ⟨ht1,ht2⟩
  · rw [ht1] at h1
    rw [ht2] at h2
    exact d33_boundary_four_of_post_three r h1 h2
  · rw [ht1] at h1
    rw [ht2] at h2
    exact d33_boundary_four_of_post_three r h2 h1

theorem d33_terminal_boundary_four {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hreg : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4) :
    ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
      a ∉ AppbPatternKind.d33.pattern.removed → M.deg (r.vertex a) = 4 := by
  intro a ha hka
  exact hreg (r.vertex a) (r.vertex_mem a ha) (all_realized_vertices_connected M .d33 r a ha)
    (fun h => hka ((r.vertex_mem_removed_iff a ha).mp h))

end WaveTurbulence.Mole.AppbAlgorithm
