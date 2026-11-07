/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNonlinearChartWitness
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeCover

/-! # Existing M9 phases prove every garden-vine coordinate is local -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
variable {X : VineType} (A : FullVineChart G.molecule X U a b)
include hU R

theorem clVine_local_x (j : Fin A.indexing.shape.m) : ChartLocalWitness A (A.indexing.shape.xSlot j) := by
  apply clLocalWitness_of_bilinear_phase hU R A (A.indexing.shape.ySlot j)
    (A.indexing.shape.xSlot j) (A.indexing.shape.ySlot j) (Ne.symm (chart_x_ne_y _ j)) (-1)
  intro g r x
  simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,mul_neg_one,neg_mul,one_mul,mul_neg]
    using A.rung_s_phase 1 g r x j

theorem clVine_local_y (j : Fin A.indexing.shape.m) : ChartLocalWitness A (A.indexing.shape.ySlot j) := by
  apply clLocalWitness_of_bilinear_phase hU R A (A.indexing.shape.ySlot j)
    (A.indexing.shape.ySlot j) (A.indexing.shape.xSlot j) (chart_x_ne_y _ j) (-1)
  intro g r x
  simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,mul_neg_one,neg_mul,one_mul,mul_neg,real_inner_comm]
    using A.rung_s_phase 1 g r x j

theorem clVine_local_u0 (hn : X.IsBad = false) : ChartLocalWitness A (A.indexing.shape.uSlot hn 0) := by
  apply clLocalWitness_of_bilinear_phase hU R A (A.indexing.shape.uSlot hn 0)
    (A.indexing.shape.uSlot hn 0) (A.indexing.shape.uSlot hn 1) (chart_u_ne _ hn (by decide)) A.coreFirstSign
  intro g r x
  have he := A.core_first_phase hn 1 g r x
  exact he.trans (by ring)

theorem clVine_local_u1 (hn : X.IsBad = false) : ChartLocalWitness A (A.indexing.shape.uSlot hn 1) := by
  apply clLocalWitness_of_bilinear_phase hU R A (A.indexing.shape.uSlot hn 0)
    (A.indexing.shape.uSlot hn 1) (A.indexing.shape.uSlot hn 0) (chart_u_ne _ hn (by decide)) A.coreFirstSign
  intro g r x
  have he := A.core_first_phase hn 1 g r x
  exact he.trans (by rw [real_inner_comm]; ring)

theorem clVine_local_u2 (hn : X.IsBad = false) : ChartLocalWitness A (A.indexing.shape.uSlot hn 2) := by
  cases hlin : A.coreLinear
  · apply clLocalWitness_of_nonlinear_phase hU R A (A.indexing.shape.uSlot hn 1)
      (A.indexing.shape.uSlot hn 2) (A.indexing.shape.uSlot hn 0) (A.indexing.shape.uSlot hn 1)
      (chart_u_ne _ hn (by decide)) (chart_u_ne _ hn (by decide)) (A.coreFirstSign*A.coreSign)
    intro g r x
    have he := A.core_second_phase hn 1 g r x
    simp only [hlin,Bool.false_eq_true,ite_false] at he
    exact he.trans (by simp only [Units.val_mul,Int.cast_mul]; ring)
  · apply clLocalWitness_of_bilinear_phase hU R A (A.indexing.shape.uSlot hn 1)
      (A.indexing.shape.uSlot hn 2) (A.indexing.shape.uSlot hn 0) (chart_u_ne _ hn (by decide)) A.coreFirstSign
    intro g r x
    have he := A.core_second_phase hn 1 g r x
    simp only [hlin,ite_true] at he
    exact he.trans (by rw [real_inner_comm]; ring)

/-- The proposed local refinement follows for actual garden vines from
the existing contract phases. It is proved here, not added as an M9 premise. -/
theorem clVineChart_hasLocalDifferences : A.HasLocalDifferences := by
  intro i
  rcases chart_shape_cover A.indexing.shape i with rfl | ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨hn,c,rfl⟩
  · exact clLocalWitness_of_joint_phase hU R A
  · exact clVine_local_x hU R A j
  · exact clVine_local_y hU R A j
  · fin_cases c
    · exact clVine_local_u0 hU R A hn
    · exact clVine_local_u1 hU R A hn
    · exact clVine_local_u2 hU R A hn

end WaveTurbulence.VineEstS2
