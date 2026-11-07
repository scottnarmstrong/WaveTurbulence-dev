/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostConnectivity
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # 3S3New scenarios with outward double bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Scenario 3 cannot split its two double-bond neighbours: reattaching
vertex 1 to the side of vertex 3 would expose the single bridge 12. -/
theorem appb_s33new3_boundary_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.SameComponent (r.vertex 3) (r.vertex 4) := by
  classical
  by_contra hn
  let S := Degen.residualComponent M r.removedAtoms (r.vertex 3)
  have h3M := r.vertex_mem 3 (by decide)
  have h3Y : r.vertex 3 ∉ r.removedAtoms :=
    fun h => (show 3 ∉ AppbPatternKind.s33new3.pattern.removed by decide)
      ((r.vertex_mem_removed_iff 3 (by decide)).mp h)
  have h3S : r.vertex 3 ∈ S := (Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) _).mpr
    ⟨h3M,h3Y,Relation.EqvGen.refl _⟩
  have h4S : r.vertex 4 ∉ S := by
    intro h
    have hh := (Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) _).mp h
    exact hn ((Degen.eraseAtoms_sameComponent_iff M r.removedAtoms _ _).mpr hh.2.2)
  have hnotS (a : ℕ) (ha : a ∈ AppbPatternKind.s33new3.pattern.removed) : r.vertex a ∉ S := by
    intro h
    have hh := (Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) _).mp h
    exact hh.2.1 (mem_image_of_mem r.vertex ha)
  have h21 : r.vertex 2 ≠ r.vertex 1 := by
    intro h
    have he := r.vertex_injective (by decide : 2 ∈ AppbPatternKind.s33new3.pattern.vertices)
      (by decide : 1 ∈ AppbPatternKind.s33new3.pattern.vertices) h
    omega
  have h41 : r.vertex 4 ≠ r.vertex 1 := by
    intro h
    have he := r.vertex_injective (by decide : 4 ∈ AppbPatternKind.s33new3.pattern.vertices)
      (by decide : 1 ∈ AppbPatternKind.s33new3.pattern.vertices) h
    omega
  let C := S ∪ {r.vertex 1}
  have hc1 : r.vertex 1 ∈ C := mem_union_right _ (mem_singleton_self _)
  have hc2 : r.vertex 2 ∉ C := by simp only [C,mem_union,mem_singleton,hnotS 2 (by decide),h21,or_self,not_false_eq_true]
  have hc3 : r.vertex 3 ∈ C := mem_union_left _ h3S
  have hc4 : r.vertex 4 ∉ C := by simp only [C,mem_union,mem_singleton,h4S,h41,or_self,not_false_eq_true]
  have hT : ({r.vertex 1} : Finset V) ⊆ r.removedAtoms := by
    intro v hv
    rw [mem_singleton.mp hv]
    exact mem_image_of_mem _ (by decide : 1 ∈ AppbPatternKind.s33new3.pattern.removed)
  have hcross := r.union_removed_cut_crossing S {r.vertex 1} hT (r.residual_cut_crossing (r.vertex 3))
  apply r.cutCount_ne_one C hcross hbridge
  change (∑ i : Fin 5, if
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,4)][i].1) ∈ C ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,4)][i].2) ∉ C) ∨
    (r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,4)][i].1) ∉ C ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,4),(2,4)][i].2) ∈ C) then 1 else 0) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num [hc1,hc2,hc3,hc4]

/-- Scenario 3's full post graph is connected, including all ambient atoms. -/
theorem appb_s33new3_post_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
  have hp := appb_s33new3_boundary_connected M r hbridge
  apply r.post_connected_of_displayed hconn (by decide)
  intro a ha hka b hb hkb
  have ha' : a = 3 ∨ a = 4 := by
    have ht : AppbPatternKind.s33new3.pattern.vertices = {1,2,3,4} := by decide
    rw [ht] at ha
    simp only [mem_insert,mem_singleton] at ha
    have hk : a ≠ 1 ∧ a ≠ 2 := by simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton,not_or] using hka
    omega
  have hb' : b = 3 ∨ b = 4 := by
    have ht : AppbPatternKind.s33new3.pattern.vertices = {1,2,3,4} := by decide
    rw [ht] at hb
    simp only [mem_insert,mem_singleton] at hb
    have hk : b ≠ 1 ∧ b ≠ 2 := by simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton,not_or] using hkb
    omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact Relation.EqvGen.refl _
  · exact hp
  · exact hp.symm
  · exact Relation.EqvGen.refl _

end WaveTurbulence.Mole
