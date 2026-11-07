/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SwapBoundary
public import WaveTurbulence.Foundations.FinalCount.AppBS33SplitLabels
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentsOfCount
public import WaveTurbulence.Foundations.FinalCount.AppBS33Topology
import Mathlib.Tactic

/-! # Canonical boundary labels for the source split 3S3 operation

The interchange of labels 5 and 6 changes neither removed atoms nor any
physical graph data. It is performed before the source direction tests.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_canonical_split_exists (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (hF : r.post.numComponents = 2) :
    ∃ r' : AppbRealization M AppbPatternKind.s33.pattern,
      r'.removedAtoms = r.removedAtoms ∧ AppbS33SplitTopology M r' := by
  obtain ⟨h4,hpair⟩ := appb_s33_split_side_labels M r hc hb hF
  have h34 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4) :=
    fun h => h4 ((r.residual_vertex_mem_iff 3 4 (by decide) (by decide)).mpr h)
  have hTwo := appb_twoComponents_of_count r.post hF
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide)) h34
  rcases hpair with ⟨h5,h6⟩ | ⟨h6,h5⟩
  · have h35 := (r.residual_vertex_mem_iff 3 5 (by decide) (by decide)).mp h5
    have h36 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 6) :=
      fun h => h6 ((r.residual_vertex_mem_iff 3 6 (by decide) (by decide)).mpr h)
    have h46 := appb_sameComponent_of_two_of_not r.post hF
      (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide))
      (r.vertex_mem_post 6 (by decide) (by decide)) h34 h36
    exact ⟨r,rfl,hTwo,h35,h46⟩
  · have h36 := (r.residual_vertex_mem_iff 3 6 (by decide) (by decide)).mp h6
    have h35 : ¬r.post.SameComponent (r.vertex 3) (r.vertex 5) :=
      fun h => h5 ((r.residual_vertex_mem_iff 3 5 (by decide) (by decide)).mpr h)
    have h45 := appb_sameComponent_of_two_of_not r.post hF
      (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide))
      (r.vertex_mem_post 5 (by decide) (by decide)) h34 h35
    refine ⟨r.s33SwapBoundary,r.s33SwapBoundary_removed,?_,?_,?_⟩
    · change TwoComponents (Degen.eraseAtoms M r.s33SwapBoundary.removedAtoms)
        (Degen.eraseAtoms M r.s33SwapBoundary.removedAtoms).atoms (r.vertex 3) (r.vertex 4)
      rw [r.s33SwapBoundary_removed]
      exact hTwo
    · change r.s33SwapBoundary.post.SameComponent (r.vertex 3) (r.vertex 6)
      exact (r.s33SwapBoundary_sameComponent _ _).mpr h36
    · change r.s33SwapBoundary.post.SameComponent (r.vertex 4) (r.vertex 5)
      exact (r.s33SwapBoundary_sameComponent _ _).mpr h45

end WaveTurbulence.Mole
