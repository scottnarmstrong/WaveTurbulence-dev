/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementCommutation

/-! # Both literal inserted subtree shapes at incomparable source roots -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subtree_replaceNodeForest_incomp {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (s : TTree) :
    Comb.subtree (Comb.replaceNodeForest tree a s b.1.1) b.1.2 = some (Comb.nodeSubtree b) := by
  by_cases hi : b.1.1 = a.1.1
  · have hp : ¬ a.1.2 <+: b.1.2 := fun h => hab.1 ⟨hi.symm,h⟩
    have hq : ¬ b.1.2 <+: a.1.2 := fun h => hab.2 ⟨hi,h⟩
    rw [Comb.replaceNodeForest,hi,Function.update_self,Comb.subtree_replaceAt_disjoint _ _ _ hp hq]
    have he := Comb.nodeSubtree_spec b
    rw [hi] at he
    exact he
  · rw [Comb.replaceNodeForest,Function.update_of_ne hi]
    exact Comb.nodeSubtree_spec b

theorem twoRootReplacement_subtrees {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (s r : TTree) :
    let F := Comb.replaceNodeForest tree a s
    let H := Function.update F b.1.1 (Comb.replaceAt (F b.1.1) b.1.2 r)
    Comb.subtree (H a.1.1) a.1.2 = some s ∧ Comb.subtree (H b.1.1) b.1.2 = some r := by
  dsimp only
  constructor
  · by_cases hi : a.1.1 = b.1.1
    · have hp : ¬ b.1.2 <+: a.1.2 := fun h => hab.2 ⟨hi.symm,h⟩
      have hq : ¬ a.1.2 <+: b.1.2 := fun h => hab.1 ⟨hi,h⟩
      rw [hi,Function.update_self,Comb.subtree_replaceAt_disjoint _ _ _ hp hq]
      rw [Comb.replaceNodeForest,← hi,Function.update_self]
      exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec a) s
    · rw [Function.update_of_ne hi,Comb.replaceNodeForest,Function.update_self]
      exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec a) s
  · rw [Function.update_self]
    exact Comb.subtree_replaceAt (subtree_replaceNodeForest_incomp tree a b hab s) r

end WaveTurbulence.Reg.Skeleton
