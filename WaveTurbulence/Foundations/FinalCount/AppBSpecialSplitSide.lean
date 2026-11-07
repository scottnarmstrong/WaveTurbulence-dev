/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostComponentBound
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
import Mathlib.Tactic

/-! # The two sides of a residual special bond after degree-three removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbSpecialSplitSide {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33new3.pattern) : Finset V :=
  Degen.residualComponent M r.removedAtoms (r.vertex 3) ∪ {r.vertex 1}

theorem appb_special_post_separates (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    ¬ r.post.SameComponent (r.vertex 3) (r.vertex 4) := by
  intro hp
  have hlabels : ∀ b ∈ AppbPatternKind.s33new3.pattern.vertices,
      b ∉ AppbPatternKind.s33new3.pattern.removed → b = 3 ∨ b = 4 := by decide
  have hconn := r.post_connected_of_boundary_representative 3 hc (by decide) (by
    intro b hb hkb
    rcases hlabels b hb hkb with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact hp)
  have hh := numComponents_eq_one r.post
    ⟨r.vertex 3,r.vertex_mem_post 3 (by decide) (by decide)⟩ hconn
  omega

theorem appb_special_split_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    r.vertex 1 ∈ appbSpecialSplitSide r ∧ r.vertex 2 ∉ appbSpecialSplitSide r ∧
      r.vertex 3 ∈ appbSpecialSplitSide r ∧ r.vertex 4 ∉ appbSpecialSplitSide r := by
  have hn2 := r.removed_vertex_not_in_residual 3 2 (by decide)
  have hm3 : r.vertex 3 ∈ Degen.residualComponent M r.removedAtoms (r.vertex 3) :=
    (r.residual_vertex_mem_iff 3 3 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have hn4 : r.vertex 4 ∉ Degen.residualComponent M r.removedAtoms (r.vertex 3) := fun h =>
    appb_special_post_separates M r hc hF ((r.residual_vertex_mem_iff 3 4 (by decide) (by decide)).mp h)
  have hn21 : r.vertex 2 ≠ r.vertex 1 := (r.vertex_eq_iff 2 1 (by decide) (by decide)).not.mpr (by decide)
  have hn41 : r.vertex 4 ≠ r.vertex 1 := (r.vertex_eq_iff 4 1 (by decide) (by decide)).not.mpr (by decide)
  simp only [appbSpecialSplitSide,mem_union,mem_singleton,hn2,hm3,hn4,hn21,hn41,
    false_or,true_or,or_true,not_false_eq_true,and_self]

theorem appb_special_split_side_crossing (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    appbCrossingBonds M (appbSpecialSplitSide r) = {(r.edge ⟨0,by decide⟩).val} := by
  have hsub := r.union_removed_cut_crossing
    (Degen.residualComponent M r.removedAtoms (r.vertex 3)) {r.vertex 1}
    (singleton_subset_iff.mpr (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.s33new3.pattern.removed by decide)))
    (r.residual_cut_crossing (r.vertex 3))
  obtain ⟨h1,h2,h3,h4⟩ := appb_special_split_side_labels M r hc hF
  ext x
  constructor
  · intro hx
    let i := r.edge.symm ⟨x,hsub hx⟩
    have he : (r.edge i).val = x := congrArg Subtype.val (r.edge.apply_symm_apply ⟨x,hsub hx⟩)
    have hh := (r.edge_cut_cross_iff (appbSpecialSplitSide r) i).mp (he.symm ▸ (mem_filter.mp hx).2)
    have hi : i = ⟨0,by decide⟩ := by
      generalize hgen : i = j at hh ⊢
      clear hgen
      fin_cases j
      · rfl
      all_goals first
        | change ((r.vertex 1 ∈ appbSpecialSplitSide r ∧ r.vertex 3 ∉ appbSpecialSplitSide r) ∨
            (r.vertex 1 ∉ appbSpecialSplitSide r ∧ r.vertex 3 ∈ appbSpecialSplitSide r)) at hh
          simp only [h1,h3,not_true_eq_false,and_false,false_and,or_self] at hh
        | change ((r.vertex 2 ∈ appbSpecialSplitSide r ∧ r.vertex 4 ∉ appbSpecialSplitSide r) ∨
            (r.vertex 2 ∉ appbSpecialSplitSide r ∧ r.vertex 4 ∈ appbSpecialSplitSide r)) at hh
          simp only [h2,h4,not_false_eq_true,and_false,false_and,or_self] at hh
    exact mem_singleton.mpr (he.symm.trans (congrArg (fun i => (r.edge i).val) hi))
  · intro hx
    have he := mem_singleton.mp hx
    subst x
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp (r.edge ⟨0,by decide⟩).property).1,?_⟩
    apply (r.edge_cut_cross_iff (appbSpecialSplitSide r) ⟨0,by decide⟩).mpr
    change ((r.vertex 1 ∈ appbSpecialSplitSide r ∧ r.vertex 2 ∉ appbSpecialSplitSide r) ∨
      (r.vertex 1 ∉ appbSpecialSplitSide r ∧ r.vertex 2 ∈ appbSpecialSplitSide r))
    simp only [h1,h2,not_false_eq_true,true_and,true_or]

end WaveTurbulence.Mole
