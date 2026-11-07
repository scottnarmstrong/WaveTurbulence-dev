/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SideLeafExpansion
public import WaveTurbulence.Foundations.VineEst.VineEstS2.HeavyChild
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SubtreeLeafCounts

/-! # Actual side-leaf support cardinality for a heavy-child predecessor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

noncomputable def heavyBranchChild (v : GBranch tree) : Fin 3 :=
  heavyChild (fun i => (v.child i).leavesBelow.card)

theorem card_sideLeaves_eq (v : GBranch tree) (i : Fin 3) :
    (sideLeaves v i).card = ∑ j ∈ Finset.univ.erase i, (v.child j).leavesBelow.card := by
  classical
  have hsub : (v.child i).leavesBelow ⊆ v.toNode.leavesBelow := by
    intro ℓ hℓ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (GBranch.isDesc_child v i).trans (Finset.mem_filter.mp hℓ).2⟩
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hs : v.toNode.leavesBelow.card = ∑ j : Fin 3, (v.child j).leavesBelow.card := by
    simpa only [Finset.sum_const,smul_eq_mul,mul_one] using v.sum_leavesBelow (fun _ => (1:ℕ))
  have he := Finset.sum_erase_add Finset.univ (fun j => (v.child j).leavesBelow.card) (Finset.mem_univ i)
  change (sideLeaves v i).card + (v.child i).leavesBelow.card = _ at hc
  omega

/-- Every actual predecessor side sum has at most twice the second-largest
child subtree leaf count, before any pairing cancellation. -/
theorem card_sideLeaves_heavy_le (v : GBranch tree) :
    (sideLeaves v (heavyBranchChild v)).card ≤
      2*medianThree (leafCount (Comb.nodeSubtree (v.child 0)))
        (leafCount (Comb.nodeSubtree (v.child 1))) (leafCount (Comb.nodeSubtree (v.child 2))) := by
  rw [card_sideLeaves_eq]
  have h := sideChildCost_le (fun i => (v.child i).leavesBelow.card)
  simpa only [heavyBranchChild,card_leavesBelow_eq] using h

end WaveTurbulence.VineEstS2
