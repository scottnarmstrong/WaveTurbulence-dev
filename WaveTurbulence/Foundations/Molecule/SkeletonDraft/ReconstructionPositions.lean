/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NodeSlots
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Literal ordered source positions under regular-tree inflation

A branch code is inserted above its original branching node. Its lone path is
therefore traversed before taking any original ordered child step.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Upper attachment address of an actual skeleton node after inflating its ancestors. -/
def inflatedPosition {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a : GNode S.tree) : Address w :=
  if h : a.1.2 = [] then a.1 else
    addrExt (inflatedPosition S X (a.parent h).toNode)
      ((X (a.parent h)).lonePath ++ [a.1.2.getLast h])
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hpos : a.1.2.length ≠ 0 := fun he => h (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

@[simp] theorem inflatedPosition_root {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain) (j : Fin w) :
    inflatedPosition S X (GNode.root S.tree j) = (j,[]) := by
  rw [inflatedPosition]
  rfl

/-- Ordered children attach below the complete regular-tree lone path. -/
theorem inflatedPosition_child {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (b : GBranch S.tree) (i : Fin 3) :
    inflatedPosition S X (b.child i) =
      addrExt (inflatedPosition S X b.toNode) ((X b).lonePath ++ [i]) := by
  rw [inflatedPosition,dite_eq_right (child_nonroot b i),parent_child]
  congr 1
  exact congrArg (fun j => (X b).lonePath ++ [j]) (List.getLast_append_singleton b.1.2)

end WaveTurbulence.Reg.Skeleton
