/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeSkeletonExistence

/-! # Literal trivial gardens, the zero-order case of the source skeleton theorem -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- DH21-2 Definition 4.1: every source tree is trivial, with its actual root matching retained. -/
def IsTrivialGarden {w : ℕ} (G : Garden w) : Prop := G.IsPlain ∧ ∀ j, G.tree j = .leaf

theorem tree_eq_leaf_of_order_zero (t : TTree) (ht : t.order = 0) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node l m r => simp only [TTree.order] at ht; omega

theorem IsTrivialGarden.order_eq_zero {w : ℕ} {G : Garden w} (h : IsTrivialGarden G) : G.order = 0 := by
  simp [Garden.order,h.2,TTree.order]

theorem isTrivialGarden_iff_order_zero {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    IsTrivialGarden G ↔ G.order = 0 := by
  constructor
  · exact IsTrivialGarden.order_eq_zero
  · intro ho
    refine ⟨hG,fun j => tree_eq_leaf_of_order_zero (G.tree j) ?_⟩
    have hj : (G.tree j).order ≤ G.order := by
      change (G.tree j).order ≤ ∑ i, (G.tree i).order
      exact Finset.single_le_sum (f := fun i => (G.tree i).order) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega

theorem IsTrivialGarden.isPrimeGarden {w : ℕ} {G : Garden w} (h : IsTrivialGarden G) : IsPrimeGarden G := by
  refine ⟨h.1,?_⟩
  rintro ⟨M⟩
  have hb := M.first.2
  rw [h.2] at hb
  exact Finset.notMem_empty _ hb

end WaveTurbulence.Reg.Skeleton
