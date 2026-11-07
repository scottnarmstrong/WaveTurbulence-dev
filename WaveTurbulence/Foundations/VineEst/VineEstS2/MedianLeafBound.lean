/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees

/-! # The local second-largest-subtree inequality (DH21 Lemma 6.6) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- The second maximum of three leaf counts. -/
def medianThree (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

private theorem ordered_leaf_bound {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (a+b+c)*b ≤ 3*(a*b*c) := by
  calc
    (a+b+c)*b ≤ (3*c)*b := Nat.mul_le_mul_right b (by omega)
    _ ≤ 3*(a*b*c) := by
      have hm : b*c ≤ a*(b*c) := by
        simpa only [one_mul] using Nat.mul_le_mul_right (b*c) ha
      nlinarith only [hm]

/-- The division-free induction step of DH21 auxineq. -/
theorem medianThree_leaf_bound (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (a+b+c)*medianThree a b c ≤ 3*(a*b*c) := by
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · simpa only [medianThree,min_eq_left hab,max_eq_right hab,min_eq_left hbc,
        max_eq_right hab] using ordered_leaf_bound ha hab hbc
    · have hcb : c ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbc)
      by_cases hac : a ≤ c
      · have he := ordered_leaf_bound ha hac hcb
        simpa only [medianThree,min_eq_left hab,max_eq_right hab,min_eq_right hcb,
          max_eq_right hac] using (show (a+b+c)*c ≤ 3*(a*b*c) by nlinarith only [he])
      · have hca : c ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hac)
        have he := ordered_leaf_bound hc hca hab
        simpa only [medianThree,min_eq_left hab,max_eq_right hab,min_eq_right hcb,
          max_eq_left hca] using (show (a+b+c)*a ≤ 3*(a*b*c) by nlinarith only [he])
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    by_cases hac : a ≤ c
    · have he := ordered_leaf_bound hb hba hac
      simpa only [medianThree,min_eq_right hba,max_eq_left hba,min_eq_left hac,
        max_eq_right hba] using (show (a+b+c)*a ≤ 3*(a*b*c) by nlinarith only [he])
    · have hca : c ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hac)
      by_cases hbc : b ≤ c
      · have he := ordered_leaf_bound hb hbc hca
        simpa only [medianThree,min_eq_right hba,max_eq_left hba,min_eq_right hca,
          max_eq_right hbc] using (show (a+b+c)*c ≤ 3*(a*b*c) by nlinarith only [he])
      · have hcb : c ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbc)
        have he := ordered_leaf_bound hc hcb hba
        simpa only [medianThree,min_eq_right hba,max_eq_left hba,min_eq_right hca,
          max_eq_left hcb] using (show (a+b+c)*b ≤ 3*(a*b*c) by nlinarith only [he])

end WaveTurbulence.VineEstS2
