/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCriteria

/-! # Exact signed side-subtree expansion for a predecessor relation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

noncomputable def sideLeaves {w : ℕ} {tree : Fin w → TTree}
    (v : GBranch tree) (i : Fin 3) : Finset (GLeaf tree) :=
  v.toNode.leavesBelow \ (v.child i).leavesBelow

/-- The signed value at a parent minus its chosen child's signed value is
exactly the signed leaf sum in the other two subtrees. -/
theorem signed_predecessor_side_sum {w : ℕ} {tree : Fin w → TTree}
    {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ) (κ : GNode tree → E)
    (hκ : ∀ v : GBranch tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (v : GBranch tree) (i : Fin 3) :
    (nodeSign sig v.1 : ℤ) • κ v.toNode - (nodeSign sig (v.child i).1 : ℤ) • κ (v.child i) =
      ∑ ℓ ∈ sideLeaves v i, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode := by
  classical
  have hsub : (v.child i).leavesBelow ⊆ v.toNode.leavesBelow := by
    intro ℓ hℓ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (GBranch.isDesc_child v i).trans (Finset.mem_filter.mp hℓ).2⟩
  have he := congrArg₂ (fun x y : E => x-y) (WaveTurbulence.sum_rule sig κ hκ v.toNode)
    (WaveTurbulence.sum_rule sig κ hκ (v.child i))
  have hs : (∑ ℓ ∈ sideLeaves v i, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode) =
      (∑ ℓ ∈ v.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode) -
        ∑ ℓ ∈ (v.child i).leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode :=
    eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)
  exact he.trans hs.symm

end WaveTurbulence.VineEstS2
