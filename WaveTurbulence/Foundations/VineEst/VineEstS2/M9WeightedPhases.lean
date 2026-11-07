/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract

/-! # Weighted source phases in the exact signed sumint normal forms -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

/-- The two actual rung phases combine with the difference of their clocks,
including the VII junction slot and the minimal typeII. -/
theorem chart_rung_weighted_phase (A : FullVineChart M X S a b) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (j : Fin A.indexing.shape.m)
    (t s tOut : ℝ) :
    (t-tOut)*nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.xSlot j) +
      (s-tOut)*nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.ySlot j) =
    2*((t-s)*inner ℝ (x (A.indexing.shape.xSlot j)) (x (A.indexing.shape.ySlot j)) +
      (t-tOut)*inner ℝ r ((A.ζc j 0 : ℝ) • x (A.indexing.shape.xSlot j) +
        (A.ζc j 1 : ℝ) • x (A.indexing.shape.ySlot j) + (A.ζc j 2 : ℝ) • r)) := by
  rw [A.rung_t_phase,A.rung_s_phase]
  ring

/-- The lower-joint phase uses the exact factor2 in the source normalization. -/
theorem chart_joint_weighted_phase (A : FullVineChart M X S a b) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (t tOut : ℝ) :
    (t-tOut)*nodeResonance A.indexing ((A.chart g r).symm x).1 g r A.indexing.shape.x0 =
      2*((t-tOut)*inner ℝ r (x A.indexing.shape.x0)) := by
  rw [A.joint_phase]
  ring

/-- Signed core phases retain both the checked common sign and the F79
relative nonlinear sign. No positive-first normalization is used. -/
theorem chart_core_weighted_phase (A : FullVineChart M X S a b) (hn : X.IsBad = false) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (τ : Fin 3 → ℝ) (tOut : ℝ) :
    (∑ c : Fin 3, (τ c-tOut)*nodeResonance A.indexing ((A.chart g r).symm x).1 g r
      (A.indexing.shape.uSlot hn c)) =
    2*((τ 0-τ 2)*(((A.coreFirstSign : ℤ) : ℝ)*
      inner ℝ (x (A.indexing.shape.uSlot hn 0)) (x (A.indexing.shape.uSlot hn 1))) +
      (τ 1-τ 2)*(((A.coreFirstSign : ℤ) : ℝ)*(if A.coreLinear then
        inner ℝ (x (A.indexing.shape.uSlot hn 0)) (x (A.indexing.shape.uSlot hn 2))
        else (((A.coreSign : ℤ) : ℝ)*inner ℝ (x (A.indexing.shape.uSlot hn 2))
          (x (A.indexing.shape.uSlot hn 0)+x (A.indexing.shape.uSlot hn 1)-x (A.indexing.shape.uSlot hn 2))))) +
      (τ 2-tOut)*inner ℝ r ((A.ξc 0 : ℝ) • x (A.indexing.shape.uSlot hn 0) +
        (A.ξc 1 : ℝ) • x (A.indexing.shape.uSlot hn 1) +
        (A.ξc 2 : ℝ) • x (A.indexing.shape.uSlot hn 2) + (A.ξc 3 : ℝ) • r)) := by
  have hsum := A.core_sum_phase hn d g r x
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ] at hsum ⊢
  simp only [Fin.sum_univ_zero,add_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hsum ⊢
  have h0 := A.core_first_phase hn d g r x
  have h1 := A.core_second_phase hn d g r x
  have h2 : nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.uSlot hn 2) =
      2*inner ℝ r ((A.ξc 0 : ℝ) • x (A.indexing.shape.uSlot hn 0) +
        (A.ξc 1 : ℝ) • x (A.indexing.shape.uSlot hn 1) +
        (A.ξc 2 : ℝ) • x (A.indexing.shape.uSlot hn 2) + (A.ξc 3 : ℝ) • r) -
      nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.uSlot hn 0) -
      nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.uSlot hn 1) := by
    linarith only [hsum]
  rw [h2,h0,h1]
  ring

end WaveTurbulence.VineEstS2
