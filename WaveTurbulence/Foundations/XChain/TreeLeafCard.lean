/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraft
/-! Exact leaf-degree bookkeeping for ternary trees and their ordered forests. -/
public section
namespace WaveTurbulence.Induct
open Finset TTree

theorem tree_card_leaves_eq : ∀ T : TTree, T.leaves.card = 2 * T.order + 1
  | .leaf => rfl
  | .node l m r => by
    have hpre : ∀ (i : Fin 3) (S : Finset TTree.Path), (TTree.pre i S).card = S.card := fun i S =>
      card_image_of_injective _ List.cons_injective
    have hdisj : ∀ {i j : Fin 3}, i ≠ j → ∀ S T : Finset TTree.Path,
        Disjoint (TTree.pre i S) (TTree.pre j T) := by
      intro i j hij S T
      rw [disjoint_left]
      intro p hp hq
      obtain ⟨q, _, rfl⟩ := TTree.mem_pre.mp hp
      exact hij (TTree.cons_mem_pre.mp hq).1.symm
    rw [TTree.leaves, card_union_of_disjoint, card_union_of_disjoint, hpre, hpre, hpre,
      tree_card_leaves_eq l, tree_card_leaves_eq m, tree_card_leaves_eq r, TTree.order]
    · omega
    · exact hdisj (by decide) _ _
    · exact disjoint_union_left.mpr ⟨hdisj (by decide) _ _, hdisj (by decide) _ _⟩

theorem forest_card_leaves_eq {w : ℕ} (top : Fin w → TTree) :
    Fintype.card (GLeaf top) = 2 * (∑ j, (top j).order) + w := by
  have he := Fintype.card_congr (forestLeafSigmaEquiv top)
  simp only [Fintype.card_sigma, Fintype.card_coe] at he
  rw [he]
  simp_rw [tree_card_leaves_eq]
  rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

end WaveTurbulence.Induct
