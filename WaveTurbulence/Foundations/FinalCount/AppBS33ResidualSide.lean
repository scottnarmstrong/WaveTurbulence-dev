/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentsSeparation
import Mathlib.Tactic

/-! # The actual 35 side of the split 3S3 residual graph -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33Side {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : Finset V :=
  Degen.residualComponent M r.removedAtoms (r.vertex 3)

theorem appb_s33_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hgeom : AppbS33SplitGeometry M r) :
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
  exact hnot (Relation.EqvGen.trans _ _ _ h36 hgeom.2.2.1.symm)

end WaveTurbulence.Mole
