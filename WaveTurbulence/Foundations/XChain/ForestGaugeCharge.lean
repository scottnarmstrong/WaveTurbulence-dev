/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestRootWeights
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
/-! Any partition of an unbalanced top forest has an unbalanced input block. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_root_leaf_weights {w : ℕ} (top : Fin w → TTree) {M : Type*} [AddCommMonoid M]
    (f : GLeaf top → M) :
    (∑ j, ∑ l ∈ (GNode.root top j).leavesBelow, f l) = ∑ l, f l := by
  classical
  simp_rw [root_leavesBelow_eq_filter]
  exact sum_fiberwise univ (fun l : GLeaf top => l.1.1) f

theorem sum_forest_leaf_sign {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ) :
    (∑ l : GLeaf top, (nodeSign sig l.1 : ℤ)) = ∑ j, (sig j : ℤ) := by
  have hc : IsBranchConsistent (fun _ : GNode top => (1 : ℤ)) := by intro b; norm_num
  have hroot (j : Fin w) : (sig j : ℤ) =
      ∑ l ∈ (GNode.root top j).leavesBelow, (nodeSign sig l.1 : ℤ) := by
    have h := sum_rule sig (fun _ : GNode top => (1 : ℤ)) hc (GNode.root top j)
    have hs : nodeSign sig (GNode.root top j).1 = sig j := by
      simp [nodeSign, GNode.root, TTree.pathSign]
    rw [hs] at h
    simpa only [zsmul_eq_mul, Int.cast_id, mul_one] using h
  rw [← sum_root_leaf_weights top (fun l => (nodeSign sig l.1 : ℤ))]
  exact sum_congr rfl (fun j _ => (hroot j).symm)

theorem sum_finpartition_blocks {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {s : Finset α} (P : Finpartition s) (f : α → M) :
    (∑ B : P.parts, ∑ a ∈ B.1, f a) = ∑ a ∈ s, f a := by
  classical
  rw [sum_coe_sort P.parts (fun B => ∑ a ∈ B, f a)]
  have he := sum_biUnion (f := f) P.supIndep.pairwiseDisjoint
  rw [P.biUnion_parts] at he
  exact he.symm

theorem exists_unbalanced_leaf_block {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ)
    (hs : ∑ j, (sig j : ℤ) ≠ 0) (P : Finpartition (univ : Finset (GLeaf top))) :
    ∃ B : P.parts, ∑ l ∈ B.1, (nodeSign sig l.1 : ℤ) ≠ 0 := by
  classical
  by_contra! h
  have he := sum_finpartition_blocks P (fun l => (nodeSign sig l.1 : ℤ))
  simp only [h, sum_const_zero, sum_forest_leaf_sign] at he
  exact hs he.symm

end WaveTurbulence.Induct
