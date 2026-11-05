/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflateNodeEquations

/-! # Every reconstructed subtree occurs at its literal transported source position -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.forest_subtree_position {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (a : GNode S.tree) :
    Comb.subtree (D.forest hS (inflatedPosition S D.tree a).1) (inflatedPosition S D.tree a).2 =
      some (D.inflateNode hS a) := by
  by_cases hp : a.1.2 = []
  · have ha : a = GNode.root S.tree a.1.1 := Subtype.ext (Prod.ext rfl hp)
    conv_lhs => rw [ha,inflatedPosition_root]
    simp only [Comb.subtree,ReconstructionData.forest]
    exact congrArg (fun z => some (D.inflateNode hS z)) ha.symm
  · let b := a.parent hp
    let i := a.1.2.getLast hp
    have ha : b.child i = a := child_parent a hp
    have ht := D.forest_subtree_position hS b.toNode
    have hc : Comb.subtree (D.forest hS (inflatedPosition S D.tree (b.child i)).1)
        (inflatedPosition S D.tree (b.child i)).2 = some (D.inflateNode hS (b.child i)) := by
      rw [inflatedPosition_child]
      change Comb.subtree (D.forest hS (inflatedPosition S D.tree b.toNode).1)
        ((inflatedPosition S D.tree b.toNode).2 ++ ((D.tree b).lonePath ++ [i])) = _
      rw [Comb.subtree_append,ht]
      exact D.inflateNode_subtree_child hS b i
    exact ha ▸ hc
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

end WaveTurbulence.Reg.Skeleton
