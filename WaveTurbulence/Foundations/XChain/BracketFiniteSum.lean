/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
/-! Finite momentum sums admit a product of leaf brackets with explicit constants. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem jbr_add_le_two_mul {d : ℕ} (x y : Mom d) :
    jbr (x + y) ≤ 2 * jbr x * jbr y := by
  have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  exact (jbr_add_le x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (jbr_pos x).le) (jbr_pos y).le)

theorem jbr_finset_sum_le {α : Type*} {d : ℕ} (s : Finset α) (f : α → Mom d) :
    jbr (∑ a ∈ s, f a) ≤ 2 ^ s.card * ∏ a ∈ s, jbr (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jbr]
  | @insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, prod_insert ha, pow_succ]
    calc
      jbr (f a + ∑ b ∈ s, f b) ≤ 2 * jbr (f a) * jbr (∑ b ∈ s, f b) := jbr_add_le_two_mul _ _
      _ ≤ 2 * jbr (f a) * (2 ^ s.card * ∏ b ∈ s, jbr (f b)) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (by norm_num) (jbr_pos _).le)
      _ = _ := by ring

end WaveTurbulence.Induct
