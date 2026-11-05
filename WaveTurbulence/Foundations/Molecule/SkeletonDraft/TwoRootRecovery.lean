/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TwoRootReplacementShapes

/-! # Replacing two incomparable subtrees and restoring both original shapes is the identity -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem twoRootReplacement_restore {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (s r : TTree) :
    let F := Function.update (Comb.replaceNodeForest tree a s) b.1.1
      (Comb.replaceAt (Comb.replaceNodeForest tree a s b.1.1) b.1.2 r)
    let A := Function.update F a.1.1 (Comb.replaceAt (F a.1.1) a.1.2 (Comb.nodeSubtree a))
    Function.update A b.1.1 (Comb.replaceAt (A b.1.1) b.1.2 (Comb.nodeSubtree b)) = tree := by
  dsimp only
  funext j
  simp only [Comb.replaceNodeForest]
  by_cases hi : a.1.1 = b.1.1
  · have hp : ¬ a.1.2 <+: b.1.2 := fun h => hab.1 ⟨hi,h⟩
    have hq : ¬ b.1.2 <+: a.1.2 := fun h => hab.2 ⟨hi.symm,h⟩
    by_cases hj : j = b.1.1
    · subst j
      simp only [hi,Function.update_self]
      rw [replaceAt_commute _ b.1.2 a.1.2 hq hp r (Comb.nodeSubtree a)]
      have ha := (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec a) s (Comb.nodeSubtree a)).trans
        (Comb.replaceAt_self (Comb.nodeSubtree_spec a))
      rw [hi] at ha
      rw [ha]
      exact (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec b) r (Comb.nodeSubtree b)).trans
        (Comb.replaceAt_self (Comb.nodeSubtree_spec b))
    · have hja : j ≠ a.1.1 := by simpa only [hi] using hj
      simp only [Function.update_of_ne hj,Function.update_of_ne hja]
  · by_cases hj : j = a.1.1
    · subst j
      simp only [Function.update_self,Function.update_of_ne hi]
      exact (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec a) s (Comb.nodeSubtree a)).trans
        (Comb.replaceAt_self (Comb.nodeSubtree_spec a))
    · by_cases hk : j = b.1.1
      · subst j
        simp only [Function.update_self,Function.update_of_ne (Ne.symm hi)]
        exact (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec b) r (Comb.nodeSubtree b)).trans
          (Comb.replaceAt_self (Comb.nodeSubtree_spec b))
      · simp only [Function.update_of_ne hj,Function.update_of_ne hk]

end WaveTurbulence.Reg.Skeleton
