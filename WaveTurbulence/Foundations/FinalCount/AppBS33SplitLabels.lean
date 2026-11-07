/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33CutFormula
public import WaveTurbulence.Foundations.FinalCount.AppBS33ResidualSide
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentPaths
import Mathlib.Tactic

/-! # The two permitted boundary pairings in a split single-pair removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem split_labels_of_tests (A B C : Prop) [Decidable A] [Decidable B] [Decidable C]
    (hS : 1+(if A then 1 else 0)+(if B then 1 else 0)+(if C then 1 else 0) ≠ (1 : ℕ))
    (hC : 1+(if ¬A then 1 else 0)+(if B then 1 else 0)+(if C then 1 else 0) ≠ (1 : ℕ))
    (hT : (if ¬A then 1 else 0)+(if ¬B then 1 else 0)+(if ¬C then 1 else 0) ≠ (1 : ℕ))
    (hn : ¬(A ∧ B ∧ C)) : ¬A ∧ ((B ∧ ¬C) ∨ (C ∧ ¬B)) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hCC : C
  all_goals simp_all

theorem appb_s33_split_side_labels (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (hF : r.post.numComponents = 2) :
    r.vertex 4 ∉ appbS33Side r ∧
      ((r.vertex 5 ∈ appbS33Side r ∧ r.vertex 6 ∉ appbS33Side r) ∨
       (r.vertex 6 ∈ appbS33Side r ∧ r.vertex 5 ∉ appbS33Side r)) := by
  classical
  let S := appbS33Side r
  have h1 : r.vertex 1 ∉ S := r.removed_vertex_not_in_residual 3 1 (by decide)
  have h2 : r.vertex 2 ∉ S := r.removed_vertex_not_in_residual 3 2 (by decide)
  have h3 : r.vertex 3 ∈ S := (r.residual_vertex_mem_iff 3 3 (by decide) (by decide)).mpr (Relation.EqvGen.refl _)
  have hnotall : ¬(r.vertex 4 ∈ S ∧ r.vertex 5 ∈ S ∧ r.vertex 6 ∈ S) := by
    rintro ⟨h4,h5,h6⟩
    have hp := r.post_connected_of_boundary_representative 3 hc (by decide) (by
      intro a ha hka
      have ha' : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
        have hV : AppbPatternKind.s33.pattern.vertices = {1,2,3,4,5,6} := by decide
        have hK : AppbPatternKind.s33.pattern.removed = {1,2} := by decide
        rw [hV] at ha
        rw [hK] at hka
        simp only [mem_insert,mem_singleton] at ha hka
        tauto
      have hm : r.vertex a ∈ S := by
        rcases ha' with rfl | rfl | rfl | rfl <;> assumption
      exact (r.residual_vertex_mem_iff 3 a ha hka).mp hm)
    have hf := numComponents_eq_one r.post ⟨r.vertex 3,r.vertex_mem_post 3 (by decide) (by decide)⟩ hp
    omega
  let C := S ∪ {r.vertex 1}
  let T := S ∪ r.removedAtoms
  have hmemC (a : ℕ) (ha : a ∈ AppbPatternKind.s33.pattern.vertices) :
      r.vertex a ∈ C ↔ r.vertex a ∈ S ∨ a = 1 := by
    rw [mem_union,mem_singleton,r.vertex_eq_iff a 1 ha (by decide)]
  have hmemT (a : ℕ) (ha : a ∈ AppbPatternKind.s33.pattern.vertices) :
      r.vertex a ∈ T ↔ r.vertex a ∈ S ∨ a ∈ AppbPatternKind.s33.pattern.removed := by
    rw [mem_union,r.vertex_mem_removed_iff a ha]
  have hcross := r.residual_cut_crossing (r.vertex 3)
  have hsub : ({r.vertex 1} : Finset V) ⊆ r.removedAtoms :=
    singleton_subset_iff.mpr (mem_image_of_mem _ (by decide))
  have hS := r.cutCount_ne_one S hcross hb
  have hC := r.cutCount_ne_one C (r.union_removed_cut_crossing S {r.vertex 1} hsub hcross) hb
  have hT := r.cutCount_ne_one T (r.union_removed_cut_crossing S r.removedAtoms (Subset.refl _) hcross) hb
  rw [appb_s33_cut_formula] at hS hC hT
  have hC1 := hmemC 1 (by decide)
  have hC2 := hmemC 2 (by decide)
  have hC3 := hmemC 3 (by decide)
  have hC4 := hmemC 4 (by decide)
  have hC5 := hmemC 5 (by decide)
  have hC6 := hmemC 6 (by decide)
  have hT1 : r.vertex 1 ∈ T := mem_union_right _ (mem_image_of_mem _ (by decide))
  have hT2 : r.vertex 2 ∈ T := mem_union_right _ (mem_image_of_mem _ (by decide))
  have hTK (a : ℕ) (ha : a ∈ AppbPatternKind.s33.pattern.vertices)
      (hk : a ∉ AppbPatternKind.s33.pattern.removed) : r.vertex a ∈ T ↔ r.vertex a ∈ S := by
    rw [hmemT a ha]
    exact or_iff_left hk
  have hT3 := hTK 3 (by decide) (by decide)
  have hT4 := hTK 4 (by decide) (by decide)
  have hT5 := hTK 5 (by decide) (by decide)
  have hT6 := hTK 6 (by decide) (by decide)
  norm_num only [hC1,hC2,hC3,hC4,hC5,hC6,hT1,hT2,hT3,hT4,hT5,hT6,
    h1,h2,h3,Nat.reduceEqDiff] at hS hC hT
  apply split_labels_of_tests (r.vertex 4 ∈ S) (r.vertex 5 ∈ S) (r.vertex 6 ∈ S) _ _ _ hnotall
  · simpa using hS
  · simpa using hC
  · simpa using hT

end WaveTurbulence.Mole
