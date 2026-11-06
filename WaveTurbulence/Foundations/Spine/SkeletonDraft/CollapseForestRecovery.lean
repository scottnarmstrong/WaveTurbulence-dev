/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementCommutation

/-! # Exact recovery after collapsing two incomparable subtrees -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Restoring both original rooted trees reverses their simultaneous collapse. -/
theorem collapsePairForest_recover {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) :
    let C := collapsePairForest tree a b hab
    let A := Function.update C a.1.1 (Comb.replaceAt (C a.1.1) a.1.2 (Comb.nodeSubtree a))
    Function.update A b.1.1 (Comb.replaceAt (A b.1.1) b.1.2 (Comb.nodeSubtree b)) = tree := by
  dsimp only
  funext j
  change (Function.update
    (Function.update
      (Function.update (Function.update tree a.1.1 (Comb.replaceAt (tree a.1.1) a.1.2 .leaf))
        b.1.1 (Comb.replaceAt ((Function.update tree a.1.1 (Comb.replaceAt (tree a.1.1) a.1.2 .leaf)) b.1.1) b.1.2 .leaf))
      a.1.1 _) b.1.1 _) j = tree j
  simp only [collapsePairForest,Comb.collapseNodeForest,Comb.replaceNodeForest,Comb.collapseOtherNode]
  by_cases hi : a.1.1 = b.1.1
  · have hp : ¬ a.1.2 <+: b.1.2 := fun h => hab.1 ⟨hi,h⟩
    have hq : ¬ b.1.2 <+: a.1.2 := fun h => hab.2 ⟨hi.symm,h⟩
    by_cases hj : j = b.1.1
    · subst j
      simp only [hi,Function.update_self]
      rw [replaceAt_commute _ b.1.2 a.1.2 hq hp .leaf (Comb.nodeSubtree a)]
      have ha := Comb.graft_collapse_eq (Comb.nodeSubtree_spec a)
      change Comb.replaceAt (Comb.replaceAt (tree a.1.1) a.1.2 .leaf) a.1.2 (Comb.nodeSubtree a) = tree a.1.1 at ha
      rw [hi] at ha
      rw [ha]
      exact Comb.graft_collapse_eq (Comb.nodeSubtree_spec b)
    · have hja : j ≠ a.1.1 := by simpa only [hi] using hj
      simp only [Function.update_of_ne hj,Function.update_of_ne hja]
  · by_cases hj : j = a.1.1
    · subst j
      simp only [Function.update_self,Function.update_of_ne hi]
      exact Comb.graft_collapse_eq (Comb.nodeSubtree_spec a)
    · by_cases hk : j = b.1.1
      · subst j
        simp only [Function.update_self,Function.update_of_ne (Ne.symm hi)]
        exact Comb.graft_collapse_eq (Comb.nodeSubtree_spec b)
      · simp only [Function.update_of_ne hj,Function.update_of_ne hk]

end WaveTurbulence.Reg.Skeleton
