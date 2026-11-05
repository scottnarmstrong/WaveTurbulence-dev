/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionChainBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreEmbedding

/-! # Actual inherited core labels in any decoded target garden -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

noncomputable def ReconstructionData.decodedCoreBranch {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G)
    (b : GBranch S.tree) : GBranch G.tree :=
  ⟨D.corePosition b,by
    have he := (Comb.subtree_branching_iff (D.decoded_subtree_core hS hd b) []).mp
      (by simp [node3,TTree.branching])
    simpa only [List.append_nil] using he⟩

/-- The source branch identities survive injectively at their exact target addresses. -/
noncomputable def ReconstructionData.decodedCoreEmbedding {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) {G : Garden w} (hd : D.Decodes hS G) :
    GBranch S.tree ↪ GBranch G.tree where
  toFun := D.decodedCoreBranch hS hd
  inj' := fun _ _ he => D.corePosition_injective (congrArg (fun b : GBranch G.tree => b.1) he)

end WaveTurbulence.Reg.Skeleton
