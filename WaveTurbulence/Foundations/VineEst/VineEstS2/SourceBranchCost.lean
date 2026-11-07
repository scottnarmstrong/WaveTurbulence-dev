/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.PathBranchCost

/-! # The literal source branch-cost product equals the proved recursive budget -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem optionLeafCount_child (v : GBranch tree) (i : Fin 3) :
    optionLeafCount (Comb.subtree (tree v.1.1) (v.1.2++[i])) = (v.child i).leavesBelow.card := by
  rw [card_leavesBelow_eq]
  have he := Comb.nodeSubtree_spec (v.child i)
  change Comb.subtree (tree v.1.1) (v.1.2++[i]) = some (Comb.nodeSubtree (v.child i)) at he
  unfold optionLeafCount
  rw [he,Option.getD_some]

theorem pathBranchCost_eq_source (v : GBranch tree) :
    pathBranchCost (tree v.1.1) v.1.2 = branchPredecessorCost v := by
  unfold pathBranchCost branchPredecessorCost
  rw [optionLeafCount_child v 0,optionLeafCount_child v 1,optionLeafCount_child v 2]

noncomputable def singleTreeBranchEquiv (T : TTree) :
    GBranch (fun _ : Fin 1 => T) ≃ ↥T.branching where
  toFun v := ⟨v.1.2,v.2⟩
  invFun p := ⟨(0,p.1),p.2⟩
  left_inv _v := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

/-- The cost budget is attached to every actual forest branch, with no
uninterpreted factor family remaining. -/
theorem prod_branchPredecessorCost (T : TTree) :
    (∏ v : GBranch (fun _ : Fin 1 => T), branchPredecessorCost v) = predecessorCostProduct T := by
  classical
  calc
    _ = ∏ v : GBranch (fun _ : Fin 1 => T), pathBranchCost T v.1.2 := by
      apply Finset.prod_congr rfl
      intro v _
      exact (pathBranchCost_eq_source v).symm
    _ = ∏ p : ↥T.branching, pathBranchCost T p.1 :=
      (singleTreeBranchEquiv T).prod_comp (fun p => pathBranchCost T p.1)
    _ = ∏ p ∈ T.branching, pathBranchCost T p := by rw [Finset.prod_coe_sort]
    _ = _ := prod_pathBranchCost T

end WaveTurbulence.VineEstS2
