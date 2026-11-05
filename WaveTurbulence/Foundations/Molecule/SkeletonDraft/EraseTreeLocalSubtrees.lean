/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionTreeUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflateNodeLocalCongruence

/-! # Removing one branch context preserves all disjoint or lower reconstructed subtrees -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseTree_inflateNode_of_not_below {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) (a : GNode S.tree)
    (ha : ¬ Below a.1 b.1) : (D.eraseTree b).inflateNode hS a = D.inflateNode hS a := by
  apply (D.eraseTree b).inflateNode_congr_below D hS a
  · intro c hc
    exact D.eraseTree_other b c (fun he => ha (he ▸ hc))
  · intro ℓ _
    rfl

theorem ReconstructionData.eraseTree_inflateNode_child {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) (i : Fin 3) :
    (D.eraseTree b).inflateNode hS (b.child i) = D.inflateNode hS (b.child i) := by
  apply D.eraseTree_inflateNode_of_not_below hS b
  intro h
  have hl := h.2.length_le
  change (b.1.2 ++ [i]).length ≤ b.1.2.length at hl
  simp only [List.length_append,List.length_singleton] at hl
  omega

theorem ReconstructionData.eraseTree_inflateNode_at {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.eraseTree b).inflateNode hS b.toNode = node3 (fun i => D.inflateNode hS (b.child i)) := by
  rw [(D.eraseTree b).inflateNode_branch,D.eraseTree_at]
  change node3 (fun i => (D.eraseTree b).inflateNode hS (b.child i)) = _
  exact congrArg node3 (funext (D.eraseTree_inflateNode_child hS b))

end WaveTurbulence.Reg.Skeleton
