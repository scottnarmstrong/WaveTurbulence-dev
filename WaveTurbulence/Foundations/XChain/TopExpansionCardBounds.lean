/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeShapeCode
public import WaveTurbulence.Foundations.XChain.PartitionCardBound
public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
public import WaveTurbulence.Foundations.XChain.TopLeafCardBound
/-! Explicit finite counts for the literal cmattr top forests and irreducible leaf partitions. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem card_TrTree_le (N : ℕ) : Fintype.card (TrTree N) ≤ 3 ^ (3 * N + 1) := by
  let e : TrTree N ≃ {T : TTree // T.order ≤ N} :=
    { toFun := fun T => ⟨T.1, mem_truncatedTrees.mp T.2⟩
      invFun := fun T => ⟨T.1, mem_truncatedTrees.mpr T.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card] at he
  exact he.trans_le (card_bounded_trees_le N)

theorem card_topForests_le (w N : ℕ) :
    Fintype.card (Fin w → TrTree N) ≤ (3 ^ (3 * N + 1)) ^ w := by
  rw [Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_left (card_TrTree_le N) w

theorem card_leafPartitions_le {w N : ℕ} (top : Fin w → TTree)
    (ht : ∀ j, (top j).order ≤ N) :
    Nat.card (Finpartition (univ : Finset (GLeaf top))) ≤
      (2 ^ (w * (2 * N + 1))) ^ (w * (2 * N + 1)) := by
  have he := forest_card_leaves_le top ht
  exact card_finpartitions_le.trans
    ((Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide : 0 < 2) he) _).trans
      (Nat.pow_le_pow_right (by positivity) he))

end WaveTurbulence.Induct
