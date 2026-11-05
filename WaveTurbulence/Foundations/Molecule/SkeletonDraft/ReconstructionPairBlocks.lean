/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionForest

/-! # Uniform finite indexing of every regular replacement pair block -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

abbrev ReplacementSlot {w : ℕ} (S : Garden w) := SourcePair S ⊕ GBranch S.tree

noncomputable def ReconstructionData.pairBlock {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : ReplacementSlot S → Finset (Pair w)
  | .inl p => ((D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)).toFinset
  | .inr b => ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)).toFinset

theorem ReconstructionData.attachmentPairs_eq_blocks {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    D.attachmentPairs hS = Finset.univ.biUnion (D.pairBlock hS) := by
  classical
  ext q
  simp only [ReconstructionData.attachmentPairs,Finset.mem_union,Finset.mem_biUnion,
    Finset.mem_univ,true_and]
  constructor
  · rintro (⟨p,hp⟩ | ⟨b,hb⟩)
    · exact ⟨.inl p,hp⟩
    · exact ⟨.inr b,hb⟩
  · rintro ⟨p,hp⟩
    cases p with
    | inl p => exact Or.inl ⟨p,hp⟩
    | inr b => exact Or.inr ⟨b,hp⟩

end WaveTurbulence.Reg.Skeleton
