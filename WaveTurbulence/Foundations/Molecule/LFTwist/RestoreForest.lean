/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementForest

/-! # Restoring the original subtree undoes one literal forest replacement -/

public section
namespace WaveTurbulence.LFTwist
open TTree

/-- Valid-root replacement is undone by restoring its actual original subtree. -/
theorem replaceNodeForest_restore {w : ℕ} (tree : Fin w → TTree)
    (a : GNode tree) (s : TTree) (a' : GNode (Comb.replaceNodeForest tree a s))
    (ha : a'.1 = a.1) :
    Comb.replaceNodeForest (Comb.replaceNodeForest tree a s) a' (Comb.nodeSubtree a) = tree := by
  have hi := congrArg Prod.fst ha
  have hp := congrArg Prod.snd ha
  funext j
  change Function.update (Function.update tree a.1.1 (Comb.replaceAt (tree a.1.1) a.1.2 s))
    a'.1.1 (Comb.replaceAt
      (Function.update tree a.1.1 (Comb.replaceAt (tree a.1.1) a.1.2 s) a'.1.1)
      a'.1.2 (Comb.nodeSubtree a)) j = tree j
  simp only [hi, hp, Function.update_self]
  by_cases hj : j = a.1.1
  · subst j
    rw [Function.update_self]
    exact (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec a) s (Comb.nodeSubtree a)).trans
      (Comb.replaceAt_self (Comb.nodeSubtree_spec a))
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

end WaveTurbulence.LFTwist
