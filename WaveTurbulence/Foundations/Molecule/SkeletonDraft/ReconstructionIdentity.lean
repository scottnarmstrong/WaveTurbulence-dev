/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionForest

/-! # Trivial replacement data reproduce the exact original forest and positions -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_identity {w : ℕ} (S : Garden w) (a : GNode S.tree) :
    inflatedPosition S (ReconstructionData.identity S).tree a = a.1 := by
  rw [inflatedPosition]
  split_ifs with h
  · rfl
  · rw [inflatedPosition_identity S (a.parent h).toNode]
    change addrExt (a.parent h).1 [a.1.2.getLast h] = a.1
    exact congrArg (fun z : GNode S.tree => z.1) (child_parent a h)
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hp : a.1.2.length ≠ 0 := fun he => h (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

theorem ReconstructionData.identity_leafTree {w : ℕ} (S : Garden w) (hS : S.IsPlain)
    (ℓ : GLeaf S.tree) : (ReconstructionData.identity S).leafTree hS ℓ = .leaf := by
  simp [ReconstructionData.leafTree,ReconstructionData.identity,RegCpl.trees,treeOfSign]

theorem ReconstructionData.identity_inflateNode {w : ℕ} (S : Garden w) (hS : S.IsPlain)
    (a : GNode S.tree) : (ReconstructionData.identity S).inflateNode hS a = Comb.nodeSubtree a := by
  rw [ReconstructionData.inflateNode]
  split
  next ha =>
    exact (ReconstructionData.identity_leafTree S hS _).trans ha.symm
  next l m r ha =>
    let b := branchOfSubtree a l m r ha
    change node3 (fun i => (ReconstructionData.identity S).inflateNode hS (b.child i)) = Comb.nodeSubtree a
    have he : node3 (fun i => (ReconstructionData.identity S).inflateNode hS (b.child i)) =
        node3 (fun i => Comb.nodeSubtree (b.child i)) :=
      congrArg node3 (funext (fun i => ReconstructionData.identity_inflateNode S hS (b.child i)))
    exact he.trans (nodeSubtree_branch S.tree b).symm

termination_by (Comb.nodeSubtree a).order
decreasing_by exact nodeSubtree_child_order_lt S.tree _ _

end WaveTurbulence.Reg.Skeleton
