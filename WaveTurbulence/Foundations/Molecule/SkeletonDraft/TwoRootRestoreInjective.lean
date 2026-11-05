/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TwoRootRecovery
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleGraftForest

/-! # A two-leaf source forest is recovered by restoring both insertion roots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.insertCouple_tree_restore {w : ℕ} (R : Raw w) (x y : Address w)
    (hR : R.PairSite x y) (Q : RegCpl) :
    let F := (R.insertCouple x y Q).tree
    let A := Function.update F x.1 (Comb.replaceAt (F x.1) x.2 .leaf)
    Function.update A y.1 (Comb.replaceAt (A y.1) y.2 .leaf) = R.tree := by
  let a := (GLeaf.toNode (⟨x,hR.leftLeaf⟩ : GLeaf R.tree))
  let b := (GLeaf.toNode (⟨y,hR.rightLeaf⟩ : GLeaf R.tree))
  have ha : Comb.nodeSubtree a = .leaf := Option.some.inj
    ((Comb.nodeSubtree_spec a).symm.trans (Comb.subtree_of_mem_leaves hR.leftLeaf))
  have hb : Comb.nodeSubtree b = .leaf := Option.some.inj
    ((Comb.nodeSubtree_spec b).symm.trans (Comb.subtree_of_mem_leaves hR.rightLeaf))
  have hr := twoRootReplacement_restore R.tree a b hR.incomparable Q.trees.1 Q.trees.2
  rw [ha,hb] at hr
  simp only [Raw.insertCouple,setAt_eq_replaceAt]
  exact hr

theorem Raw.insertCouple_tree_injective {w : ℕ} (R T : Raw w) (x y : Address w)
    (hR : R.PairSite x y) (hT : T.PairSite x y) (Q : RegCpl)
    (he : (R.insertCouple x y Q).tree = (T.insertCouple x y Q).tree) : R.tree = T.tree := by
  let restore (F : Fin w → TTree) :=
    let A := Function.update F x.1 (Comb.replaceAt (F x.1) x.2 .leaf)
    Function.update A y.1 (Comb.replaceAt (A y.1) y.2 .leaf)
  exact (R.insertCouple_tree_restore x y hR Q).symm.trans
    ((congrArg restore he).trans (T.insertCouple_tree_restore x y hT Q))

end WaveTurbulence.Reg.Skeleton
