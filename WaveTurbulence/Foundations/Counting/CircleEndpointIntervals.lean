/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointGeometry
import Mathlib.Tactic

/-!
# Exact integer windows for both halves of an endpoint block

The artificial octant cut and dyadic cuts retain their strict endpoints.
Each half is an actual consecutive integer interval, uniformly in a real
center. These identities connect local integer-window estimates to the
finite sets consumed by the circle discrepancy transfer.
-/

public section

namespace WaveTurbulence.Counting

/-- Right endpoint columns, with the strict octant and inner block cuts. -/
@[expose] noncomputable def circleEndpointRight (R c U : ℝ) : Finset ℤ :=
  Finset.Icc (max ⌈c+R-2*U⌉ (⌊c+R/Real.sqrt 2⌋+1)) (⌈c+R-U⌉-1)

/-- Left endpoint columns, with exactly the reflected endpoint conventions. -/
@[expose] noncomputable def circleEndpointLeft (R c U : ℝ) : Finset ℤ :=
  Finset.Icc (⌊c-R+U⌋+1) (min ⌊c-R+2*U⌋ (⌈c-R/Real.sqrt 2⌉-1))

theorem mem_circleEndpointRight (R c U : ℝ) (n : ℤ) :
    n ∈ circleEndpointRight R c U ↔
      c+R-2*U ≤ (n:ℝ) ∧ c+R/Real.sqrt 2 < n ∧ (n:ℝ) < c+R-U := by
  simp only [circleEndpointRight,Finset.mem_Icc,max_le_iff]
  have h1 : ⌊c+R/Real.sqrt 2⌋+1 ≤ n ↔ c+R/Real.sqrt 2 < n := by
    rw [show ⌊c+R/Real.sqrt 2⌋+1 ≤ n ↔ ⌊c+R/Real.sqrt 2⌋ < n by omega,Int.floor_lt]
  have h2 : n ≤ ⌈c+R-U⌉-1 ↔ (n:ℝ) < c+R-U := by
    rw [show n ≤ ⌈c+R-U⌉-1 ↔ n < ⌈c+R-U⌉ by omega,Int.lt_ceil]
  rw [Int.ceil_le,h1,h2]
  tauto

theorem mem_circleEndpointLeft (R c U : ℝ) (n : ℤ) :
    n ∈ circleEndpointLeft R c U ↔
      c-R+U < (n:ℝ) ∧ (n:ℝ) ≤ c-R+2*U ∧ (n:ℝ) < c-R/Real.sqrt 2 := by
  simp only [circleEndpointLeft,Finset.mem_Icc,le_min_iff]
  have h1 : ⌊c-R+U⌋+1 ≤ n ↔ c-R+U < (n:ℝ) := by
    rw [show ⌊c-R+U⌋+1 ≤ n ↔ ⌊c-R+U⌋ < n by omega,Int.floor_lt]
  have h2 : n ≤ ⌈c-R/Real.sqrt 2⌉-1 ↔ (n:ℝ) < c-R/Real.sqrt 2 := by
    rw [show n ≤ ⌈c-R/Real.sqrt 2⌉-1 ↔ n < ⌈c-R/Real.sqrt 2⌉ by omega,Int.lt_ceil]
  rw [h1,Int.le_floor,h2]

/-- An actual two-sided endpoint block is the disjoint union of two
consecutive integer windows. -/
theorem circle_endpoint_block_eq_union {R c U : ℝ} (hR : 0 < R) (_hU : 0 < U) :
    ((integerInterval (c-R) (c+R)).filter (fun n : ℤ =>
      R/Real.sqrt 2 < |(n:ℝ)-c| ∧ U < R-|(n:ℝ)-c| ∧ R-|(n:ℝ)-c| ≤ 2*U)) =
      circleEndpointLeft R c U ∪ circleEndpointRight R c U := by
  classical
  have hcut : 0 < R/Real.sqrt 2 := by positivity
  ext n
  simp only [Finset.mem_filter,mem_integerInterval,Finset.mem_union,
    mem_circleEndpointLeft,mem_circleEndpointRight]
  by_cases hn : c ≤ (n:ℝ)
  · rw [abs_of_nonneg (sub_nonneg.mpr hn)]
    constructor
    · rintro ⟨_hb,ho,hl,hu⟩
      right
      constructor
      · linarith only [hu]
      constructor <;> linarith only [ho,hl]
    · rintro (hl | hr)
      · have := hl.2.2
        linarith only [this,hn,hcut]
      · refine ⟨⟨?_,?_⟩,?_,?_,?_⟩ <;> linarith only [hr.1,hr.2.1,hr.2.2,hn,hR,_hU]
  · have hn' : (n:ℝ) ≤ c := le_of_not_ge hn
    rw [abs_of_nonpos (sub_nonpos.mpr hn')]
    constructor
    · rintro ⟨_hb,ho,hl,hu⟩
      left
      constructor
      · linarith only [hl]
      constructor <;> linarith only [ho,hu]
    · rintro (hl | hr)
      · refine ⟨⟨?_,?_⟩,?_,?_,?_⟩ <;> linarith only [hl.1,hl.2.1,hl.2.2,hn',hR,_hU]
      · have := hr.2.1
        linarith only [this,hn',hcut]

/-- The two exact integer windows have no shared columns. -/
theorem disjoint_circleEndpointLeft_right {R c U : ℝ} (hR : 0 < R) :
    Disjoint (circleEndpointLeft R c U) (circleEndpointRight R c U) := by
  apply Finset.disjoint_left.mpr
  intro n hn hl
  have hleft := (mem_circleEndpointLeft R c U n).mp hn
  have hright := (mem_circleEndpointRight R c U n).mp hl
  have hcut : 0 < R/Real.sqrt 2 := by positivity
  linarith only [hleft.2.2,hright.2.1,hcut]

/-- Exact sum decomposition, valid for any summand. -/
theorem sum_circle_endpoint_block_eq {E : Type*} [AddCommMonoid E]
    (f : ℤ → E) {R c U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    (∑ n ∈ (integerInterval (c-R) (c+R)).filter (fun n : ℤ =>
      R/Real.sqrt 2 < |(n:ℝ)-c| ∧ U < R-|(n:ℝ)-c| ∧ R-|(n:ℝ)-c| ≤ 2*U), f n) =
      (∑ n ∈ circleEndpointLeft R c U, f n)+(∑ n ∈ circleEndpointRight R c U, f n) := by
  classical
  rw [circle_endpoint_block_eq_union hR hU,Finset.sum_union (disjoint_circleEndpointLeft_right hR)]

end WaveTurbulence.Counting
