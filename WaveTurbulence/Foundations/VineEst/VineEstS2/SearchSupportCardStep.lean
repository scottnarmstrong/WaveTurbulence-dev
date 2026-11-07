/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SearchLeafSupport

/-! # Nested actual leaf sets and support cardinality along a heavy step -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem leavesBelow_subset_of_desc {a b : GNode tree} (h : a.IsDesc b) :
    b.leavesBelow ⊆ a.leavesBelow := by
  intro ℓ hℓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.trans (Finset.mem_filter.mp hℓ).2⟩

theorem card_sdiff_nested {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hBA : B ⊆ A) (hCB : C ⊆ B) : (A \ C).card = (A \ B).card + (B \ C).card := by
  have ha := Finset.card_sdiff_add_card_eq_card (hCB.trans hBA)
  have hb := Finset.card_sdiff_add_card_eq_card hCB
  have hc := Finset.card_sdiff_add_card_eq_card hBA
  omega

/-- Skipping one opposite-sign heavy child adds precisely its two side
subtrees to the eventual predecessor support. -/
theorem searchLeafSupport_next_card (sig : Fin w → ℤˣ) (ζ : ℤˣ) {v u : GBranch tree}
    (hu : nextHeavyBranch v = some u) (hs : nodeSign sig u.1 ≠ ζ) :
    (searchLeafSupport sig ζ v).card = (sideLeaves v (heavyBranchChild v)).card +
      (searchLeafSupport sig ζ u).card := by
  classical
  have hend := congrArg (fun q : List (GBranch tree) × Option (GBranch tree) => q.2)
    (signHeavySearch_different sig ζ hu hs)
  have hsub := leavesBelow_subset_of_desc (nextHeavyBranch_desc hu)
  have hside := congrArg (fun x : GNode tree => v.toNode.leavesBelow \ x.leavesBelow)
    (nextHeavyBranch_node hu)
  change v.toNode.leavesBelow \ u.toNode.leavesBelow = sideLeaves v (heavyBranchChild v) at hside
  have hcard := congrArg Finset.card hside
  cases he : (signHeavySearch sig ζ u).2 with
  | none =>
    simp only [searchLeafSupport,hend,he]
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hcard] at hc
    exact hc.symm
  | some z =>
    simp only [searchLeafSupport,hend,he]
    have hz := leavesBelow_subset_of_desc (signHeavySearch_target sig ζ u z he).2.2
    have hc := card_sdiff_nested hsub hz
    rw [hcard] at hc
    exact hc

end WaveTurbulence.VineEstS2
