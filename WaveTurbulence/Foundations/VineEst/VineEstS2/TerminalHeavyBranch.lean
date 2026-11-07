/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.HeavySuccessor
public import WaveTurbulence.Foundations.VineEst.VineEstS2.PositivePathCosts

/-! # A terminal heavy-child branch has exactly three leaves -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem leaf_leavesBelow (ℓ : GLeaf tree) : ℓ.toNode.leavesBelow = {ℓ} := by
  classical
  ext m
  simp only [GNode.leavesBelow,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro h
    exact (GLeaf.eq_of_isDesc h).symm
  · rintro rfl
    exact GNode.isDesc_refl _

theorem nextHeavyBranch_none_not_branch (v : GBranch tree) (hv : nextHeavyBranch v = none) :
    (v.child (heavyBranchChild v)).1.2 ∉ (tree (v.child (heavyBranchChild v)).1.1).branching := by
  classical
  unfold nextHeavyBranch at hv
  dsimp only at hv
  split at hv
  · cases hv
  · rename_i hn
    exact hn

theorem terminal_heavy_child_card (v : GBranch tree) (hv : nextHeavyBranch v = none) :
    (v.child (heavyBranchChild v)).leavesBelow.card = 1 := by
  classical
  have hn := nextHeavyBranch_none_not_branch v hv
  have hl := ((TTree.mem_nodes_iff _ _).mp (v.child (heavyBranchChild v)).2).resolve_right hn
  let ℓ : GLeaf tree := ⟨(v.child (heavyBranchChild v)).1,hl⟩
  have he := leaf_leavesBelow ℓ
  change (v.child (heavyBranchChild v)).leavesBelow = {ℓ} at he
  rw [he,Finset.card_singleton]

theorem terminal_all_children_card (v : GBranch tree) (hv : nextHeavyBranch v = none) (i : Fin 3) :
    (v.child i).leavesBelow.card = 1 := by
  apply Nat.le_antisymm
  · calc
      _ ≤ (v.child (heavyBranchChild v)).leavesBelow.card :=
        le_heavyChild (fun i => (v.child i).leavesBelow.card) i
      _ = 1 := terminal_heavy_child_card v hv
  · rw [card_leavesBelow_eq]
    unfold leafCount
    omega

theorem terminal_parent_card (v : GBranch tree) (hv : nextHeavyBranch v = none) :
    v.toNode.leavesBelow.card = 3 := by
  have hs := v.sum_leavesBelow (fun _ => (1:ℕ))
  simpa only [Finset.sum_const,smul_eq_mul,mul_one,terminal_all_children_card v hv,
    Fin.sum_univ_three,Finset.card_univ,Fintype.card_fin] using hs

theorem terminal_parent_cost (v : GBranch tree) (hv : nextHeavyBranch v = none) :
    branchPredecessorCost v = 3 := by
  unfold branchPredecessorCost
  rw [terminal_all_children_card v hv 0,terminal_all_children_card v hv 1,terminal_all_children_card v hv 2]
  rfl

end WaveTurbulence.VineEstS2
