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
