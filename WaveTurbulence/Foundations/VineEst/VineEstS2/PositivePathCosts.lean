/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SideLeafBudget
public import WaveTurbulence.Foundations.VineEst.VineEstS2.RouteProductBudget

/-! # Positive local costs dominate sign-skipping support sizes -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- An elementary finite product absorbs the sum of nonnegative costs and
one terminal leaf; this avoids a factor depending on the skipped path length. -/
theorem one_add_sum_le_prod_one_add {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) :
    1+∑ a ∈ S, f a ≤ ∏ a ∈ S, (1+f a) := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,add_zero,le_refl]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.prod_insert ha]
    calc
      _ ≤ (1+f a)*(1+∑ b ∈ S, f b) := by nlinarith only [Nat.zero_le (f a*(∑ b ∈ S, f b))]
      _ ≤ (1+f a)*(∏ b ∈ S, (1+f b)) := Nat.mul_le_mul_left _ ih

noncomputable def branchPredecessorCost {w : ℕ} {tree : Fin w → TTree} (v : GBranch tree) : ℕ :=
  3*medianThree (v.child 0).leavesBelow.card (v.child 1).leavesBelow.card (v.child 2).leavesBelow.card

theorem branchPredecessorCost_pos {w : ℕ} {tree : Fin w → TTree} (v : GBranch tree) :
    1 ≤ branchPredecessorCost v := by
  have h (i : Fin 3) : 1 ≤ (v.child i).leavesBelow.card := by
    rw [card_leavesBelow_eq]
    unfold leafCount
    omega
  unfold branchPredecessorCost medianThree
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  omega

theorem one_add_sideLeaves_le_cost {w : ℕ} {tree : Fin w → TTree} (v : GBranch tree) :
    1+(sideLeaves v (heavyBranchChild v)).card ≤ branchPredecessorCost v := by
  have hs := sideChildCost_le (fun i => (v.child i).leavesBelow.card)
  rw [card_sideLeaves_eq]
  have hm : 1 ≤ medianThree (v.child 0).leavesBelow.card (v.child 1).leavesBelow.card
      (v.child 2).leavesBelow.card := by
    have h (i : Fin 3) : 1 ≤ (v.child i).leavesBelow.card := by
      rw [card_leavesBelow_eq]
      unfold leafCount
      omega
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    unfold medianThree
    omega
  change 1+(∑ j ∈ Finset.univ.erase (heavyChild (fun i => (v.child i).leavesBelow.card)),
    (v.child j).leavesBelow.card) ≤ 3*medianThree (v.child 0).leavesBelow.card
      (v.child 1).leavesBelow.card (v.child 2).leavesBelow.card
  omega

end WaveTurbulence.VineEstS2
