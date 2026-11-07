/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PriorityTests
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
import Mathlib.Tactic

/-! # A primary or common double-pair realization supplies the source trigger -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_realization_has_pair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : HasDegreeThreePair M 2 := by
  refine ⟨r.vertex 1,r.vertex_mem 1 (by decide),r.vertex 2,r.vertex_mem 2 (by decide),?_,?_,?_,?_⟩
  · exact (r.deleted_degree 1 (by decide)).trans (by decide)
  · exact (r.deleted_degree 2 (by decide)).trans (by decide)
  · intro h
    have hh := r.vertex_injective (by decide : 1 ∈ AppbPatternKind.d33.pattern.vertices)
      (by decide : 2 ∈ AppbPatternKind.d33.pattern.vertices) h
    omega
  · exact (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)

theorem d33same_realization_has_pair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33same.pattern) : HasDegreeThreePair M 2 := by
  refine ⟨r.vertex 1,r.vertex_mem 1 (by decide),r.vertex 2,r.vertex_mem 2 (by decide),?_,?_,?_,?_⟩
  · exact (r.deleted_degree 1 (by decide)).trans (by decide)
  · exact (r.deleted_degree 2 (by decide)).trans (by decide)
  · intro h
    have hh := r.vertex_injective (by decide : 1 ∈ AppbPatternKind.d33same.pattern.vertices)
      (by decide : 2 ∈ AppbPatternKind.d33same.pattern.vertices) h
    omega
  · exact (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)

end WaveTurbulence.Mole.AppbAlgorithm
