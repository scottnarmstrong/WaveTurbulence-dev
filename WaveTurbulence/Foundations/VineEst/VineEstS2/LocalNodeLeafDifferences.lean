/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.PhysicalPredecessor

/-! # Local incidence differences have one signed leaf support -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

/-- A same-sign descendant difference cancels exactly its subtree. This
geometric lemma does not assume a desired coefficient bound. -/
theorem node_difference_leaf_sum_of_desc {E : Type*} [AddCommGroup E]
    (sig : Fin w → ℤˣ) (κ : GNode tree → E)
    (hκ : ∀ v : GBranch tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (u v : GNode tree) (hd : u.IsDesc v) (hs : nodeSign sig u.1 = nodeSign sig v.1) :
    κ u-κ v = ∑ ℓ ∈ u.leavesBelow \ v.leavesBelow,
      ((nodeSign sig u.1 : ℤ)*(nodeSign sig ℓ.1 : ℤ)) • κ ℓ.toNode := by
  classical
  have hsub : v.leavesBelow ⊆ u.leavesBelow := by
    intro ℓ hℓ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.trans (Finset.mem_filter.mp hℓ).2⟩
  have he := congrArg₂ (fun x y : E => x-y) (WaveTurbulence.sum_rule sig κ hκ u)
    (WaveTurbulence.sum_rule sig κ hκ v)
  rw [← hs] at he
  have hl := congrArg (fun x : E => (nodeSign sig u.1 : ℤ) • x) he
  simp only [smul_sub,intUnit_zsmul_twice,Finset.smul_sum,smul_smul] at hl
  rw [← Finset.sum_sdiff hsub] at hl
  simpa only [smul_sub,smul_smul,intUnit_square,one_smul,add_sub_cancel_right] using hl

/-- Opposite-sign incomparable subtrees add their signed leaf expansions;
there is no overlap that could create a coefficient of magnitude two. -/
theorem node_difference_leaf_sum_of_disjoint {E : Type*} [AddCommGroup E]
    (sig : Fin w → ℤˣ) (κ : GNode tree → E)
    (hκ : ∀ v : GBranch tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (u v : GNode tree) (hd : Disjoint u.leavesBelow v.leavesBelow)
    (hs : nodeSign sig v.1 = -nodeSign sig u.1) :
    κ u-κ v = ∑ ℓ ∈ u.leavesBelow ∪ v.leavesBelow,
      ((nodeSign sig u.1 : ℤ)*(nodeSign sig ℓ.1 : ℤ)) • κ ℓ.toNode := by
  classical
  have he := congrArg₂ (fun x y : E => x+y) (WaveTurbulence.sum_rule sig κ hκ u)
    (WaveTurbulence.sum_rule sig κ hκ v)
  rw [hs] at he
  have hl := congrArg (fun x : E => (nodeSign sig u.1 : ℤ) • x) he
  simp only [Units.val_neg,neg_smul,smul_add,smul_neg,intUnit_zsmul_twice,
    Finset.smul_sum,smul_smul,← sub_eq_add_neg] at hl
  rw [← Finset.sum_union hd] at hl
  simpa only [smul_sub,smul_smul,intUnit_square,one_smul,add_sub_cancel_right] using hl

end WaveTurbulence.VineEstS2
