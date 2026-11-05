/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.ChainContextBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeCoverage

/-! # Literal branch transport from each native regular paired-tree context -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

abbrev ChainBranchPath {w : ℕ} {S : Garden w} (D : ReconstructionData S) (b : GBranch S.tree) :=
  ↥((D.tree b).plug (nodeSign S.sig b.1) .leaf).branching

noncomputable def chainContextBranch {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : ChainBranchPath D b) : GBranch (D.forest hS) :=
  ⟨addrExt (inflatedPosition S D.tree b.toNode) q.1,by
    have hs := (D.forest_subtree_position hS b.toNode).trans
      (congrArg some (D.inflateNode_branch hS b))
    exact (Comb.subtree_branching_iff hs q.1).mp (chain_branching_subset_plug _ _ _ q.2)⟩

theorem chainContextBranch_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) : Function.Injective (chainContextBranch D hS b) := by
  intro q r he
  have hp := congrArg (fun z : GBranch (D.forest hS) => z.1.2) he
  exact Subtype.ext (List.append_cancel_left hp)

theorem chainContextBranch_mem_block {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : ChainBranchPath D b) :
    (chainContextBranch D hS b q).1 ∈ D.nodeBlock hS (.inr b) := by
  change addrExt (inflatedPosition S D.tree b.toNode) q.1 ∈
    chainNodes (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) ∪
      {addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath}
  rw [← nodeAddresses_leaf,← chain_nodeAddresses]
  exact Finset.mem_image.mpr ⟨q.1,TTree.branching_subset_nodes _ q.2,rfl⟩

theorem chainContextBranch_ne_core {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : ChainBranchPath D b) :
    chainContextBranch D hS b q ≠ D.coreBranch hS b := by
  intro he
  have hp := congrArg (fun z : GBranch (D.forest hS) => z.1.2) he
  have hq : q.1 = (D.tree b).lonePath := List.append_cancel_left hp
  apply chain_branch_not_below_hole _ _ _ q.2
  exact hq.symm ▸ List.prefix_refl _

end WaveTurbulence.RegRed
