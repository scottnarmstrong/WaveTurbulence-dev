/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9WeightedPhases

/-! # Weighted phases of one ingredient block, in exponent form -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

theorem block_joint_exponent (A : FullVineChart M X S a b) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (c tx t0 : ℝ) :
    c * nodeResonance A.indexing ((A.chart g r).symm x).1 g r A.indexing.shape.x0 * (tx - t0) =
      c * (2 * ((tx - t0) * inner ℝ r (x A.indexing.shape.x0))) := by
  have h := chart_joint_weighted_phase A g r x tx t0
  linear_combination c * h

theorem block_rung_exponent (A : FullVineChart M X S a b) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (j : Fin A.indexing.shape.m)
    (c tx ty t0 : ℝ) :
    c * nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.xSlot j) * (tx - t0) +
      c * nodeResonance A.indexing ((A.chart g r).symm x).1 g r (A.indexing.shape.ySlot j) * (ty - t0) =
    c * (2 * ((tx - ty) * inner ℝ (x (A.indexing.shape.xSlot j)) (x (A.indexing.shape.ySlot j)) +
      (tx - t0) * inner ℝ r ((A.ζc j 0 : ℝ) • x (A.indexing.shape.xSlot j) +
        (A.ζc j 1 : ℝ) • x (A.indexing.shape.ySlot j) + (A.ζc j 2 : ℝ) • r))) := by
  have h := chart_rung_weighted_phase A g r x j tx ty t0
  linear_combination c * h

theorem block_core_exponent (A : FullVineChart M X S a b) (hn : X.IsBad = false) {d : ℕ}
    (g r : Mom d) (x : Fin A.indexing.shape.n → Mom d) (τ : Fin 3 → ℝ) (c t0 : ℝ) :
    (∑ c' : Fin 3, c * nodeResonance A.indexing ((A.chart g r).symm x).1 g r
      (A.indexing.shape.uSlot hn c') * (τ c' - t0)) =
    c * (2 * ((τ 0-τ 2)*(((A.coreFirstSign : ℤ) : ℝ)*
      inner ℝ (x (A.indexing.shape.uSlot hn 0)) (x (A.indexing.shape.uSlot hn 1))) +
      (τ 1-τ 2)*(((A.coreFirstSign : ℤ) : ℝ)*(if A.coreLinear then
        inner ℝ (x (A.indexing.shape.uSlot hn 0)) (x (A.indexing.shape.uSlot hn 2))
        else (((A.coreSign : ℤ) : ℝ)*inner ℝ (x (A.indexing.shape.uSlot hn 2))
          (x (A.indexing.shape.uSlot hn 0)+x (A.indexing.shape.uSlot hn 1)-x (A.indexing.shape.uSlot hn 2))))) +
      (τ 2-t0)*inner ℝ r ((A.ξc 0 : ℝ) • x (A.indexing.shape.uSlot hn 0) +
        (A.ξc 1 : ℝ) • x (A.indexing.shape.uSlot hn 1) +
        (A.ξc 2 : ℝ) • x (A.indexing.shape.uSlot hn 2) + (A.ξc 3 : ℝ) • r))) := by
  have h := chart_core_weighted_phase A hn g r x τ t0
  have e : (∑ c' : Fin 3, c * nodeResonance A.indexing ((A.chart g r).symm x).1 g r
      (A.indexing.shape.uSlot hn c') * (τ c' - t0)) =
      c * ∑ c' : Fin 3, (τ c' - t0) * nodeResonance A.indexing ((A.chart g r).symm x).1 g r
        (A.indexing.shape.uSlot hn c') := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c' _
    ring
  rw [e, h]

theorem inner_flip_two {d : ℕ} (rc X Y : Mom d) (a b c : ℤ) :
    inner ℝ (-rc) (((-a : ℤ) : ℝ) • X + ((-b : ℤ) : ℝ) • Y + (c : ℝ) • (-rc)) =
      inner ℝ rc ((a : ℝ) • X + (b : ℝ) • Y + (c : ℝ) • rc) := by
  simp only [inner_add_right, inner_neg_left, inner_neg_right, inner_smul_right, Int.cast_neg]
  ring

theorem inner_flip_three {d : ℕ} (rc u0 u1 u2 : Mom d) (a b c e : ℤ) :
    inner ℝ (-rc) (((-a : ℤ) : ℝ) • u0 + ((-b : ℤ) : ℝ) • u1 + ((-c : ℤ) : ℝ) • u2 +
        (e : ℝ) • (-rc)) =
      inner ℝ rc ((a : ℝ) • u0 + (b : ℝ) • u1 + (c : ℝ) • u2 + (e : ℝ) • rc) := by
  simp only [inner_add_right, inner_neg_left, inner_neg_right, inner_smul_right, Int.cast_neg]
  ring

end WaveTurbulence.VineEstS2
