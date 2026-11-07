/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchRoute
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SearchSupportCardStep
public import WaveTurbulence.Foundations.VineEst.VineEstS2.TerminalHeavyBranch

/-! # The actual predecessor leaf support fits its exponential route budget -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem heavy_start_not_in_tail (sig : Fin w → ℤˣ) (ζ : ℤˣ) {v u : GBranch tree}
    (hu : nextHeavyBranch v = some u) : v ∉ (signHeavySearch sig ζ u).1 := by
  intro hv
  have hd := (signHeavySearch_route_spec sig ζ u v hv).1.2.length_le
  change u.1.2.length ≤ v.1.2.length at hd
  have hs := nextHeavyBranch_depth hu
  omega

/-- Every actual signed leaf row has support size at most the product of
local source costs along its constructed route. This is a proved counting
step, not a cost hypothesis placed on a parametrization. -/
theorem searchLeafSupport_card_le_route (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v : GBranch tree) :
    (searchLeafSupport sig ζ v).card ≤
      ∏ u ∈ (signHeavySearch sig ζ v).1.toFinset, branchPredecessorCost u := by
  classical
  induction hm : branchDepthBound tree-v.1.2.length using Nat.strong_induction_on generalizing v with
  | h n ih =>
    cases hn : nextHeavyBranch v with
    | none =>
      simp only [searchLeafSupport,signHeavySearch_none sig ζ v hn,List.toFinset_cons,
        List.toFinset_nil,Finset.insert_empty,Finset.prod_singleton]
      rw [terminal_parent_card v hn,terminal_parent_cost v hn]
    | some u =>
      by_cases hs : nodeSign sig u.1 = ζ
      · have hp : (signHeavySearch sig ζ v).1.toFinset = {v} := by
          rw [signHeavySearch_same sig ζ hn hs]
          rfl
        have hS : searchLeafSupport sig ζ v = sideLeaves v (heavyBranchChild v) := by
          unfold searchLeafSupport
          rw [signHeavySearch_same sig ζ hn hs]
          exact congrArg (fun x : GNode tree => v.toNode.leavesBelow \ x.leavesBelow) (nextHeavyBranch_node hn)
        rw [hp,Finset.prod_singleton,hS]
        have hb := one_add_sideLeaves_le_cost v
        omega
      · have hlt : branchDepthBound tree-u.1.2.length < n := by
          rw [← hm]
          exact nextHeavyBranch_measure_lt hn
        have ht := ih _ hlt u rfl
        have hnot : v ∉ (signHeavySearch sig ζ u).1.toFinset := by
          simpa only [List.mem_toFinset] using heavy_start_not_in_tail sig ζ hn
        have hp : (signHeavySearch sig ζ v).1.toFinset =
            insert v (signHeavySearch sig ζ u).1.toFinset := by
          rw [signHeavySearch_different sig ζ hn hs]
          exact List.toFinset_cons
        rw [hp,Finset.prod_insert hnot,searchLeafSupport_next_card sig ζ hn hs]
        have hc := one_add_sideLeaves_le_cost v
        have hone : 1 ≤ ∏ z ∈ (signHeavySearch sig ζ u).1.toFinset, branchPredecessorCost z :=
          Finset.one_le_prod (fun z _ => branchPredecessorCost_pos z)
        calc
          _ ≤ (sideLeaves v (heavyBranchChild v)).card +
              ∏ z ∈ (signHeavySearch sig ζ u).1.toFinset, branchPredecessorCost z := Nat.add_le_add_left ht _
          _ ≤ (1+(sideLeaves v (heavyBranchChild v)).card)*
              (∏ z ∈ (signHeavySearch sig ζ u).1.toFinset, branchPredecessorCost z) := by
            have hmul := Nat.mul_le_mul_left (sideLeaves v (heavyBranchChild v)).card hone
            nlinarith only [hmul]
          _ ≤ _ := Nat.mul_le_mul_right _ hc

end WaveTurbulence.VineEstS2
