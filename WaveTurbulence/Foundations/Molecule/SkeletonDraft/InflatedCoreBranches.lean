/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSubtrees
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns

/-! # Actual surviving core branches inside the literal reconstructed forest -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Address of the original branch below its complete regular-tree replacement. -/
def ReconstructionData.corePosition {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : Address w :=
  addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath

theorem ReconstructionData.forest_subtree_core {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    Comb.subtree (D.forest hS (D.corePosition b).1) (D.corePosition b).2 =
      some (node3 (fun i => D.inflateNode hS (b.child i))) := by
  change Comb.subtree (D.forest hS (inflatedPosition S D.tree b.toNode).1)
    ((inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath) = _
  rw [Comb.subtree_append,D.forest_subtree_position hS b.toNode]
  exact D.inflateNode_subtree_lone hS b

/-- Each actual source core branch survives as a genuine branch of the reconstructed forest. -/
noncomputable def ReconstructionData.coreBranch {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) : GBranch (D.forest hS) :=
  ⟨D.corePosition b,by
    have he := (Comb.subtree_branching_iff (D.forest_subtree_core hS b) []).mp
      (by simp [node3,TTree.branching])
    simpa only [List.append_nil] using he⟩

/-- Each original ordered child attaches directly below the surviving core branch. -/
theorem ReconstructionData.core_child_position {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) (i : Fin 3) :
    inflatedPosition S D.tree (b.child i) = addrExt (D.corePosition b) [i] := by
  rw [inflatedPosition_child]
  exact (addrExt_append _ _ _).symm

theorem ReconstructionData.corePosition_sign {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : nodeSign S.sig (D.corePosition b) = nodeSign S.sig b.1 := by
  rw [ReconstructionData.corePosition,nodeSign_addrExt,lonePath_sign,inflatedPosition_sign]
  rfl

end WaveTurbulence.Reg.Skeleton
