/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflateNodeEquations

/-! # Local dependence of reconstructed subtrees on their actual source descendants -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.inflateNode_congr_below {w : ℕ} {S : Garden w}
    (D E : ReconstructionData S) (hS : S.IsPlain) (a : GNode S.tree)
    (ht : ∀ b : GBranch S.tree, Below a.1 b.1 → D.tree b = E.tree b)
    (hl : ∀ ℓ : GLeaf S.tree, Below a.1 ℓ.1 → D.leafTree hS ℓ = E.leafTree hS ℓ) :
    D.inflateNode hS a = E.inflateNode hS a := by
  cases hs : Comb.nodeSubtree a with
  | leaf =>
    let ℓ := leafOfSubtree a hs
    have ha : ℓ.toNode = a := Subtype.ext rfl
    exact (congrArg (D.inflateNode hS) ha.symm).trans
      ((D.inflateNode_leaf hS ℓ).trans ((hl ℓ ⟨rfl,List.prefix_refl _⟩).trans
        ((E.inflateNode_leaf hS ℓ).symm.trans (congrArg (E.inflateNode hS) ha))))
  | node l m r =>
    let b := branchOfSubtree a l m r hs
    have hb : b.toNode = a := Subtype.ext rfl
    have hc (i : Fin 3) : D.inflateNode hS (b.child i) = E.inflateNode hS (b.child i) :=
      D.inflateNode_congr_below E hS (b.child i)
        (fun c hc => ht c (below_trans (below_extend a.1 [i]) hc))
        (fun ℓ hℓ => hl ℓ (below_trans (below_extend a.1 [i]) hℓ))
    have he : D.inflateNode hS b.toNode = E.inflateNode hS b.toNode := by
      rw [D.inflateNode_branch,E.inflateNode_branch,ht b ⟨rfl,List.prefix_refl _⟩]
      exact congrArg ((E.tree b).plug (nodeSign S.sig b.1)) (congrArg node3 (funext hc))
    exact (congrArg (D.inflateNode hS) hb.symm).trans (he.trans (congrArg (E.inflateNode hS) hb))
termination_by (Comb.nodeSubtree a).order
decreasing_by exact nodeSubtree_child_order_lt S.tree _ _

end WaveTurbulence.Reg.Skeleton
