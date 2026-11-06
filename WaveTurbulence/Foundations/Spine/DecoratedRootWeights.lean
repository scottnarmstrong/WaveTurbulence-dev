/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightTransfer
public import WaveTurbulence.Foundations.Canon.Basic
/-! The corrected root-to-leaf weight transfer on the exact decorated forest carrier. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

/-- Each node has a nonempty set of descendant leaves, including the trivial-tree case. -/
theorem leavesBelow_nonempty {w : ℕ} {tree : Fin w → TTree} (a : GNode tree) :
    a.leavesBelow.Nonempty := by
  obtain ⟨m, hm⟩ := Canon.odd_card_leavesBelow a
  apply Finset.card_pos.mp
  omega

/-- TARGET L2065, with leaf cardinality replacing the invalid 3*n factor at tree order zero.
The input is exactly the branching-consistent vector decoration of the source sum rule. -/
theorem exists_leaf_root_weight_bound {w d : ℕ} {tree : Fin w → TTree}
    (sig : Fin w → ℤˣ) (k : GNode tree → Mom d)
    (hcons : ∀ b : GBranch tree, k b.toNode = k (b.child 0) - k (b.child 1) + k (b.child 2))
    (a : GNode tree) (M : ℕ) :
    ∃ ℓ ∈ a.leavesBelow, jbr (k a) ^ M ≤ (a.leavesBelow.card : ℝ) ^ M * jbr (k ℓ.toNode) ^ M := by
  obtain ⟨ℓ, hℓ, h⟩ := exists_jbr_sum_units_pow_le a.leavesBelow (leavesBelow_nonempty a)
    (fun ℓ => nodeSign sig ℓ.1) (fun ℓ => k ℓ.toNode) M
  rw [← sum_rule sig k hcons a, jbr_units_smul] at h
  exact ⟨ℓ, hℓ, h⟩

end WaveTurbulence.LGSpine
