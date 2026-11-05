/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPairSite
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainIdentity

/-! # Trivial couple insertion is the literal identity at a typed source pair -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Raw.insertCouple_triv {w : ℕ} (R : Raw w) (x y : Address w) (h : R.PairSite x y) :
    R.insertCouple x y .triv = R := by
  classical
  have hx : (R.tree x.1).setAt x.2 .leaf = R.tree x.1 := by
    rw [setAt_eq_replaceAt]
    exact Comb.replaceAt_self (Comb.subtree_of_mem_leaves h.leftLeaf)
  have hy : (R.tree y.1).setAt y.2 .leaf = R.tree y.1 := by
    rw [setAt_eq_replaceAt]
    exact Comb.replaceAt_self (Comb.subtree_of_mem_leaves h.rightLeaf)
  apply Raw.ext
  · rfl
  · simp only [Raw.insertCouple,RegCpl.trees,hx,hy,Function.update_eq_self]
  · change R.pairs.erase (x,y) ∪ {(x,y)} = R.pairs
    rw [Finset.union_singleton,Finset.insert_erase h.pair_mem]

end WaveTurbulence.Reg.Skeleton
