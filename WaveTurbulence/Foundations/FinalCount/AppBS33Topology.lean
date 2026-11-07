/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33ResidualSide
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentsSeparation
import Mathlib.Tactic

/-! # The split 3S3 topology without any boundary orientation restriction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def AppbS33SplitTopology (M : Molecule V D) (r : AppbRealization M AppbPatternKind.s33.pattern) : Prop :=
  TwoComponents r.post r.post.atoms (r.vertex 3) (r.vertex 4) ∧
    r.post.SameComponent (r.vertex 3) (r.vertex 5) ∧ r.post.SameComponent (r.vertex 4) (r.vertex 6)

theorem appb_s33_side_labels_topology (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitTopology M r) :
    r.vertex 1 ∉ appbS33Side r ∧ r.vertex 2 ∉ appbS33Side r ∧
      r.vertex 3 ∈ appbS33Side r ∧ r.vertex 4 ∉ appbS33Side r ∧
      r.vertex 5 ∈ appbS33Side r ∧ r.vertex 6 ∉ appbS33Side r := by
  have hnot := appb_twoComponents_not_sameComponent r.post hgeom.1
  have hmem (a : ℕ) (ha : a ∈ AppbPatternKind.s33.pattern.vertices)
      (hk : a ∉ AppbPatternKind.s33.pattern.removed) :
      r.vertex a ∈ appbS33Side r ↔ r.post.SameComponent (r.vertex 3) (r.vertex a) :=
    r.residual_vertex_mem_iff 3 a ha hk
  refine ⟨r.removed_vertex_not_in_residual 3 1 (by decide),
    r.removed_vertex_not_in_residual 3 2 (by decide),
    (hmem 3 (by decide) (by decide)).mpr (Relation.EqvGen.refl _),
    fun h => hnot ((hmem 4 (by decide) (by decide)).mp h),
    (hmem 5 (by decide) (by decide)).mpr hgeom.2.1,?_⟩
  intro h
  have h36 := (hmem 6 (by decide) (by decide)).mp h
  exact hnot (Relation.EqvGen.trans _ _ _ h36 hgeom.2.2.symm)


theorem appb_s33_splitTopology_of_geometry {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.s33.pattern} (h : AppbS33SplitGeometry M r) :
    AppbS33SplitTopology M r := ⟨h.1,h.2.1,h.2.2.1⟩

end WaveTurbulence.Mole
