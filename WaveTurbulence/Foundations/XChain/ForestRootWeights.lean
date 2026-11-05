/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestRootBracket
/-! Multiplying rootwise momentum bounds gives the exact leaf-degree loss. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem root_leavesBelow_eq_filter {w : ℕ} (top : Fin w → TTree) (j : Fin w) :
    (GNode.root top j).leavesBelow = univ.filter (fun l : GLeaf top => l.1.1 = j) := by
  ext l
  simp [GNode.leavesBelow, GNode.IsDesc, GNode.root, GLeaf.toNode, eq_comm]

theorem prod_root_leaf_weights {w : ℕ} (top : Fin w → TTree) {M : Type*} [CommMonoid M]
    (f : GLeaf top → M) :
    (∏ j, ∏ l ∈ (GNode.root top j).leavesBelow, f l) = ∏ l, f l := by
  classical
  simp_rw [root_leavesBelow_eq_filter]
  exact prod_fiberwise univ (fun l : GLeaf top => l.1.1) f

theorem sum_root_leaf_cards {w : ℕ} (top : Fin w → TTree) :
    (∑ j, (GNode.root top j).leavesBelow.card) = Fintype.card (GLeaf top) := by
  classical
  have he := sum_fiberwise univ (fun l : GLeaf top => l.1.1) (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, card_univ] at he
  simpa only [root_leavesBelow_eq_filter] using he

theorem forest_roots_jbr_le {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) (L : ℝ) :
    (∏ j, jbr (latticePoint L (n j))) ≤
      2 ^ Fintype.card (GLeaf top) * ∏ l : GLeaf top, jbr (latticePoint L (κ.1 l.toNode)) := by
  classical
  have h := prod_le_prod₀ (s := (univ : Finset (Fin w)))
    (fun j _ => (jbr_pos _).le) (fun j _ => forest_root_jbr_le top n κ L j)
  rw [prod_mul_distrib, prod_root_leaf_weights, prod_pow_eq_pow_sum, sum_root_leaf_cards] at h
  exact h

end WaveTurbulence.Induct
