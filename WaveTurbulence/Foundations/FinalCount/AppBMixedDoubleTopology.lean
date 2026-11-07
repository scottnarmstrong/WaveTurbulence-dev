/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # 3S3New scenario 5: the double neighbour and two single neighbours -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem appb_s33new5_no_single_side (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new5.pattern) (S : Finset V)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e)
    (h1 : r.vertex 1 ∉ S) (h2 : r.vertex 2 ∉ S) (h3 : r.vertex 3 ∉ S)
    (h45 : (r.vertex 4 ∈ S ∧ r.vertex 5 ∉ S) ∨ (r.vertex 4 ∉ S ∧ r.vertex 5 ∈ S)) : False := by
  classical
  apply r.cutCount_ne_one S hcross hbridge
  change (∑ i : Fin 5, if
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].1) ∈ S ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].2) ∉ S) ∨
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].1) ∉ S ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].2) ∈ S) then 1 else 0) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  rcases h45 with ⟨h4,h5⟩ | ⟨h4,h5⟩ <;> norm_num [h1,h2,h3,h4,h5]

/-- The two single neighbours of the pair lie in the same residual
component: otherwise one side has a singleton old boundary. -/
theorem appb_s33new5_singles_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new5.pattern)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.SameComponent (r.vertex 4) (r.vertex 5) := by
  classical
  by_contra hn
  let S4 := Degen.residualComponent M r.removedAtoms (r.vertex 4)
  let S5 := Degen.residualComponent M r.removedAtoms (r.vertex 5)
  have h4S4 : r.vertex 4 ∈ S4 := (r.residual_vertex_mem_iff 4 4 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have h5S5 : r.vertex 5 ∈ S5 := (r.residual_vertex_mem_iff 5 5 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have h5S4 : r.vertex 5 ∉ S4 := fun h => hn ((r.residual_vertex_mem_iff 4 5 (by decide) (by decide)).mp h)
  have h4S5 : r.vertex 4 ∉ S5 := fun h => hn ((r.residual_vertex_mem_iff 5 4 (by decide) (by decide)).mp h).symm
  by_cases h3 : r.vertex 3 ∈ S4
  · have h3S5 : r.vertex 3 ∉ S5 := by
      intro h
      have hp43 := (r.residual_vertex_mem_iff 4 3 (by decide) (by decide)).mp h3
      have hp53 := (r.residual_vertex_mem_iff 5 3 (by decide) (by decide)).mp h
      exact hn (Relation.EqvGen.trans _ _ _ hp43 hp53.symm)
    exact appb_s33new5_no_single_side M r S5 (r.residual_cut_crossing (r.vertex 5)) hbridge
      (r.removed_vertex_not_in_residual 5 1 (by decide))
      (r.removed_vertex_not_in_residual 5 2 (by decide)) h3S5 (Or.inr ⟨h4S5,h5S5⟩)
  · exact appb_s33new5_no_single_side M r S4 (r.residual_cut_crossing (r.vertex 4)) hbridge
      (r.removed_vertex_not_in_residual 4 1 (by decide))
      (r.removed_vertex_not_in_residual 4 2 (by decide)) h3 (Or.inl ⟨h4S4,h5S4⟩)

/-- Reattaching vertex 1 to the double-neighbour side rules out its
separation from the two single neighbours. -/
theorem appb_s33new5_double_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new5.pattern)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.SameComponent (r.vertex 3) (r.vertex 4) := by
  classical
  have hp45 := appb_s33new5_singles_connected M r hbridge
  by_contra hn
  let S := Degen.residualComponent M r.removedAtoms (r.vertex 3)
  have h3S : r.vertex 3 ∈ S := (r.residual_vertex_mem_iff 3 3 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have h4S : r.vertex 4 ∉ S := fun h => hn ((r.residual_vertex_mem_iff 3 4 (by decide) (by decide)).mp h)
  have h5S : r.vertex 5 ∉ S := by
    intro h
    have hp := (r.residual_vertex_mem_iff 3 5 (by decide) (by decide)).mp h
    exact hn (Relation.EqvGen.trans _ _ _ hp hp45.symm)
  let C := S ∪ {r.vertex 1}
  have hc1 : r.vertex 1 ∈ C := mem_union_right _ (mem_singleton_self _)
  have hc3 : r.vertex 3 ∈ C := mem_union_left _ h3S
  have h2S : r.vertex 2 ∉ S := r.removed_vertex_not_in_residual 3 2 (by decide)
  have hc2 : r.vertex 2 ∉ C := by
    simp only [C,mem_union,mem_singleton,h2S,
      r.vertex_eq_iff 2 1 (by decide) (by decide),Nat.reduceEqDiff,or_self,not_false_eq_true]
  have hc4 : r.vertex 4 ∉ C := by
    simp only [C,mem_union,mem_singleton,h4S,r.vertex_eq_iff 4 1 (by decide) (by decide),
      Nat.reduceEqDiff,or_self,not_false_eq_true]
  have hc5 : r.vertex 5 ∉ C := by
    simp only [C,mem_union,mem_singleton,h5S,r.vertex_eq_iff 5 1 (by decide) (by decide),
      Nat.reduceEqDiff,or_self,not_false_eq_true]
  have hT : ({r.vertex 1} : Finset V) ⊆ r.removedAtoms := by
    intro v hv
    rw [mem_singleton.mp hv]
    exact mem_image_of_mem _ (by decide : 1 ∈ AppbPatternKind.s33new5.pattern.removed)
  have hcross := r.union_removed_cut_crossing S {r.vertex 1} hT (r.residual_cut_crossing (r.vertex 3))
  apply r.cutCount_ne_one C hcross hbridge
  change (∑ i : Fin 5, if
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].1) ∈ C ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].2) ∉ C) ∨
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].1) ∉ C ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,5)][i].2) ∈ C) then 1 else 0) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num [hc1,hc2,hc3,hc4,hc5]

/-- Scenario 5's entire actual residual graph is connected. -/
theorem appb_s33new5_post_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new5.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
  have hp34 := appb_s33new5_double_connected M r hbridge
  have hp45 := appb_s33new5_singles_connected M r hbridge
  apply r.post_connected_of_boundary_representative 3 hconn (by decide)
  intro b hb hkb
  have hcases : b = 3 ∨ b = 4 ∨ b = 5 := by
    have ht : AppbPatternKind.s33new5.pattern.vertices = {1,2,3,4,5} := by decide
    rw [ht] at hb
    simp only [mem_insert,mem_singleton] at hb
    have hk : b ≠ 1 ∧ b ≠ 2 := by simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton,not_or] using hkb
    omega
  rcases hcases with rfl | rfl | rfl
  · exact Relation.EqvGen.refl _
  · exact hp34
  · exact Relation.EqvGen.trans _ _ _ hp34 hp45

end WaveTurbulence.Mole
