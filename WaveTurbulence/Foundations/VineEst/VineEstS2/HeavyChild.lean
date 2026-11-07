/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.MedianLeafBound

/-! # An explicit heavy child and the side-subtree coefficient cost -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- Choose a largest child, with a deterministic tie convention. -/
def heavyChild (f : Fin 3 → ℕ) : Fin 3 :=
  if f 1 ≤ f 0 then (if f 2 ≤ f 0 then 0 else 2)
  else (if f 2 ≤ f 1 then 1 else 2)

theorem le_heavyChild (f : Fin 3 → ℕ) (i : Fin 3) : f i ≤ f (heavyChild f) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> unfold heavyChild <;> split_ifs <;> omega

theorem sum_three_le_max_add_median (a b c : ℕ) :
    a+b+c ≤ max (max a b) c + 2*medianThree a b c := by
  unfold medianThree
  omega

/-- Removing the largest child leaves at most twice the second-largest
subtree leaf count. This is the source coefficient-count estimate. -/
theorem sideChildCost_le (f : Fin 3 → ℕ) :
    (∑ i ∈ Finset.univ.erase (heavyChild f), f i) ≤ 2*medianThree (f 0) (f 1) (f 2) := by
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (heavyChild f))
  have hm : max (max (f 0) (f 1)) (f 2) ≤ f (heavyChild f) :=
    max_le (max_le (le_heavyChild f 0) (le_heavyChild f 1)) (le_heavyChild f 2)
  have hs := sum_three_le_max_add_median (f 0) (f 1) (f 2)
  rw [Fin.sum_univ_three] at he
  omega

end WaveTurbulence.VineEstS2
