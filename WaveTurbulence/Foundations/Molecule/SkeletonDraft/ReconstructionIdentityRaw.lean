/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentity
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # The literal reconstruction map has the exact source identity case -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.identity_forest {w : ℕ} (S : Garden w) (hS : S.IsPlain) :
    (ReconstructionData.identity S).forest hS = S.tree := by
  funext j
  rw [ReconstructionData.forest,ReconstructionData.identity_inflateNode]
  have he := Comb.nodeSubtree_spec (GNode.root S.tree j)
  simp only [GNode.root,Comb.subtree] at he
  exact (Option.some.inj he).symm

theorem ReconstructionData.identity_attachmentPairs {w : ℕ} (S : Garden w) (hS : S.IsPlain) :
    (ReconstructionData.identity S).attachmentPairs hS = sourcePairs S := by
  classical
  simp only [ReconstructionData.attachmentPairs,ReconstructionData.identity,RegCpl.pairsAt,
    RegChain.pairsAt]
  have hi (a : GNode S.tree) : inflatedPosition S (fun _ => .nil) a = a.1 := inflatedPosition_identity S a
  simp only [hi]
  change (Finset.univ.biUnion (fun p : SourcePair S => {p.1})) ∪
    (Finset.univ.biUnion (fun _ : GBranch S.tree => ∅)) = sourcePairs S
  ext p
  simp only [Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_singleton,Finset.notMem_empty,exists_false,or_false]
  constructor
  · rintro ⟨q,rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

/-- The reconstruction formula reproduces every actual source datum for identity replacements. -/
theorem ReconstructionData.identity_raw {w : ℕ} (S : Garden w) (hS : S.IsPlain) :
    (ReconstructionData.identity S).raw hS = rawOfGarden S := by
  apply Raw.ext
  · rfl
  · exact ReconstructionData.identity_forest S hS
  · exact ReconstructionData.identity_attachmentPairs S hS

end WaveTurbulence.Reg.Skeleton
