/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Grafting
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts

/-! # Forest shape surgery at a leaf pair (TARGET L846–L847)

The two slots may belong to one tree or to different trees. These operations
supply the actual tree shapes and exact counts; leaf pairings are transported
separately by the packet's embedding constructions.
-/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} (tree : Fin w → TTree)

/-- Graft a rooted tree into one leaf slot of an ordered forest. -/
@[expose] def graftLeafForest (ℓ : GLeaf tree) (s : TTree) : Fin w → TTree :=
  Function.update tree ℓ.1.1 (replaceAt (tree ℓ.1.1) ℓ.1.2 s)

/-- Grafting at a leaf adds the inserted branching order. -/
theorem graftLeafForest_order (ℓ : GLeaf tree) (s : TTree) :
    (∑ j, (graftLeafForest tree ℓ s j).order) = (∑ j, (tree j).order) + s.order := by
  have he : ∀ j, (graftLeafForest tree ℓ s j).order =
      (tree j).order + if j = ℓ.1.1 then s.order else 0 := by
    intro j
    by_cases hj : j = ℓ.1.1
    · subst j
      rw [graftLeafForest, Function.update_self, order_graft_leaf ℓ.2]
      simp
    · rw [graftLeafForest, Function.update_of_ne hj]
      simp [hj]
  simp_rw [he, Finset.sum_add_distrib]
  simp

/-- Every other old leaf survives the graft at the same global address. -/
@[expose] def graftLeafForest_other (ℓ q : GLeaf tree) (hne : q ≠ ℓ) (s : TTree) :
    GLeaf (graftLeafForest tree ℓ s) := ⟨q.1, by
  by_cases hj : q.1.1 = ℓ.1.1
  · rw [hj, graftLeafForest, Function.update_self, leaves_replaceAt_eq (subtree_of_mem_leaves ℓ.2)]
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨by rw [← hj]; exact q.2, ?_⟩
    intro hp
    apply hne
    exact (GLeaf.eq_of_isDesc (a := ℓ) (ℓ := q) ⟨hj.symm, hp⟩).symm
  · rw [graftLeafForest, Function.update_of_ne hj]
    exact q.2⟩

/-- Graft two trees into two distinct leaf slots, including slots in one tree. -/
@[expose] def graftLeafPairForest (ℓ q : GLeaf tree) (hne : q ≠ ℓ) (s r : TTree) : Fin w → TTree :=
  graftLeafForest (graftLeafForest tree ℓ s) (graftLeafForest_other tree ℓ q hne s) r

/-- Pair replacement adds both inserted tree orders. -/
theorem graftLeafPairForest_order (ℓ q : GLeaf tree) (hne : q ≠ ℓ) (s r : TTree) :
    (∑ j, (graftLeafPairForest tree ℓ q hne s r j).order) =
      (∑ j, (tree j).order) + s.order + r.order := by
  rw [graftLeafPairForest, graftLeafForest_order, graftLeafForest_order]

/-- Pair replacement removes two old leaves and adds the two inserted leaf sets. -/
theorem graftLeafPairForest_leaves (ℓ q : GLeaf tree) (hne : q ≠ ℓ) (s r : TTree) :
    Fintype.card (GLeaf (graftLeafPairForest tree ℓ q hne s r)) + 2 =
      Fintype.card (GLeaf tree) + s.leaves.card + r.leaves.card := by
  rw [card_gleaf, card_gleaf, graftLeafPairForest_order, card_leaves, card_leaves]
  omega

end WaveTurbulence.Comb
