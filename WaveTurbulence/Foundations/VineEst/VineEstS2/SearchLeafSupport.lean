/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SignSearchTarget
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SideLeafExpansion

/-! # Actual leaf support and exact sum identity of a sign-skipping predecessor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

noncomputable def searchLeafSupport (sig : Fin w → ℤˣ) (ζ : ℤˣ) (v : GBranch tree) : Finset (GLeaf tree) :=
  match (signHeavySearch sig ζ v).2 with
  | none => v.toNode.leavesBelow
  | some u => v.toNode.leavesBelow \ u.toNode.leavesBelow

noncomputable def searchSignedEndpoint {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ)
    (ζ : ℤˣ) (κ : GNode tree → E) (v : GBranch tree) : E :=
  ((signHeavySearch sig ζ v).2).elim 0 (fun u => (nodeSign sig u.1 : ℤ) • κ u.toNode)

/-- The actual leaf set, rather than an assumed signed affine row, gives the
predecessor relation. The missing predecessor uses the ordinary full leaf sum. -/
theorem searchLeafSupport_sum {E : Type*} [AddCommGroup E] (sig : Fin w → ℤˣ)
    (ζ : ℤˣ) (κ : GNode tree → E)
    (hκ : ∀ v : GBranch tree, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (v : GBranch tree) :
    (nodeSign sig v.1 : ℤ) • κ v.toNode - searchSignedEndpoint sig ζ κ v =
      ∑ ℓ ∈ searchLeafSupport sig ζ v, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode := by
  classical
  cases he : (signHeavySearch sig ζ v).2 with
  | none =>
    simp only [searchSignedEndpoint,searchLeafSupport,he,Option.elim_none]
    change (nodeSign sig v.toNode.1 : ℤ) • κ v.toNode - 0 =
      ∑ ℓ ∈ v.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode
    rw [sub_zero]
    exact WaveTurbulence.sum_rule sig κ hκ v.toNode
  | some u =>
    have hd := (signHeavySearch_target sig ζ v u he).2.2
    have hsub : u.toNode.leavesBelow ⊆ v.toNode.leavesBelow := by
      intro ℓ hℓ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.trans (Finset.mem_filter.mp hℓ).2⟩
    have hv := congrArg₂ (fun a b : E => a-b) (WaveTurbulence.sum_rule sig κ hκ v.toNode)
      (WaveTurbulence.sum_rule sig κ hκ u.toNode)
    have hs : (∑ ℓ ∈ v.toNode.leavesBelow \ u.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode) =
        (∑ ℓ ∈ v.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode) -
          ∑ ℓ ∈ u.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode :=
      eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)
    simp only [searchSignedEndpoint,searchLeafSupport,he,Option.elim_some]
    change (nodeSign sig v.toNode.1 : ℤ) • κ v.toNode - (nodeSign sig u.toNode.1 : ℤ) • κ u.toNode =
      ∑ ℓ ∈ v.toNode.leavesBelow \ u.toNode.leavesBelow, (nodeSign sig ℓ.1 : ℤ) • κ ℓ.toNode
    exact hv.trans hs.symm

end WaveTurbulence.VineEstS2
