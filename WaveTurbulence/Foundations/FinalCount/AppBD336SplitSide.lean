/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
public import WaveTurbulence.Foundations.FinalCount.AppBPostComponentBound
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
import Mathlib.Tactic

/-! # The concrete two-bond cut in the split 3D3New graph -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d336_post_separates (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    ¬ r.post.SameComponent (r.vertex 5) (r.vertex 6) := by
  intro hp
  have hlabels : ∀ b ∈ AppbPatternKind.d33new.pattern.vertices,
      b ∉ AppbPatternKind.d33new.pattern.removed → b = 5 ∨ b = 6 := by decide
  have hconn := r.post_connected_of_boundary_representative 5 hc (by decide) (by
    intro b hb hkb
    rcases hlabels b hb hkb with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact hp)
  have hh := numComponents_eq_one r.post
    ⟨r.vertex 5,r.vertex_mem_post 5 (by decide) (by decide)⟩ hconn
  omega

noncomputable def appbD336SplitSide {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern) : Finset V :=
  Degen.residualComponent M r.removedAtoms (r.vertex 5) ∪ {r.vertex 3}

theorem appb_d336_split_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    r.vertex 1 ∉ appbD336SplitSide r ∧ r.vertex 2 ∉ appbD336SplitSide r ∧
      r.vertex 3 ∈ appbD336SplitSide r ∧ r.vertex 4 ∉ appbD336SplitSide r ∧
      r.vertex 5 ∈ appbD336SplitSide r ∧ r.vertex 6 ∉ appbD336SplitSide r := by
  have hn1 := r.removed_vertex_not_in_residual 5 1 (by decide)
  have hn2 := r.removed_vertex_not_in_residual 5 2 (by decide)
  have hn4 := r.removed_vertex_not_in_residual 5 4 (by decide)
  have hm5 : r.vertex 5 ∈ Degen.residualComponent M r.removedAtoms (r.vertex 5) :=
    (r.residual_vertex_mem_iff 5 5 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have hn6 : r.vertex 6 ∉ Degen.residualComponent M r.removedAtoms (r.vertex 5) := fun h =>
    appb_d336_post_separates M r hc hF ((r.residual_vertex_mem_iff 5 6 (by decide) (by decide)).mp h)
  have hn13 : r.vertex 1 ≠ r.vertex 3 := (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  have hn23 : r.vertex 2 ≠ r.vertex 3 := (r.vertex_eq_iff 2 3 (by decide) (by decide)).not.mpr (by decide)
  have hn43 : r.vertex 4 ≠ r.vertex 3 := (r.vertex_eq_iff 4 3 (by decide) (by decide)).not.mpr (by decide)
  have hn63 : r.vertex 6 ≠ r.vertex 3 := (r.vertex_eq_iff 6 3 (by decide) (by decide)).not.mpr (by decide)
  simp only [appbD336SplitSide,mem_union,mem_singleton,hn1,hn2,hn4,hm5,hn6,hn13,hn23,hn43,hn63,
    false_or,true_or,or_true,not_false_eq_true,and_self]

end WaveTurbulence.Mole
