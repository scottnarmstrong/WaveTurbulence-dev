/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeCoverage
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.FiniteBlockInsertion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawValidityFaithfulness

/-! # Source B expansion preserves the actual regular reconstruction range -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.insertMini_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (m : MiniTreeCode) :
    (D.insertMini hS target.1 m).attachmentPairs hS = ((D.raw hS).opB target.1 m).pairs := by
  classical
  change (D.insertMini hS target.1 m).attachmentPairs hS =
    (D.attachmentPairs hS).image (fun p =>
      (relocate target.1 m.c m.lone p.1,relocate target.1 m.c m.lone p.2)) ∪ miniPairs S.sig target.1 m
  rw [D.attachmentPairs_eq_blocks hS,(D.insertMini hS target.1 m).attachmentPairs_eq_blocks hS]
  exact biUnion_image_insertion (D.pairBlock hS) ((D.insertMini hS target.1 m).pairBlock hS)
    _ (fun slot => target.1 ∈ D.nodeBlock hS slot) _
    (D.insertMini_pairBlock hS target m) (D.node_covered hS target)

theorem ReconstructionData.insertMini_decodes {w : ℕ} {S H : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (m : MiniTreeCode) (hH : H.IsPlain)
    (he : rawOfGarden H = (D.raw hS).opB target.1 m) :
    (D.insertMini hS target.1 m).Decodes hS H := by
  let E := D.insertMini hS target.1 m
  have hp : (E.raw hS).pairs = (rawOfGarden H).pairs :=
    (D.insertMini_pairs hS target m).trans (congrArg Raw.pairs he).symm
  have hs : (E.raw hS).sig = (rawOfGarden H).sig := (congrArg Raw.sig he).symm
  exact ⟨hH,Raw.eq_of_valid_sig_pairs _ _ (E.raw_valid hS) (rawOfGarden_valid H hH) hs hp⟩

theorem ReconstructionData.opB_decodes {w : ℕ} {S G H : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
    (a : Address w) (m : MiniTreeCode) (hH : H.IsPlain)
    (ha : a.2 ∈ (G.tree a.1).nodes) (he : rawOfGarden H = (rawOfGarden G).opB a m) :
    ∃ E : ReconstructionData S, E.Decodes hS H := by
  have ht := congrArg Raw.tree hd.2
  change D.forest hS = G.tree at ht
  let target : GNode (D.forest hS) := ⟨a,by rw [ht]; exact ha⟩
  refine ⟨D.insertMini hS a m,D.insertMini_decodes hS target m hH ?_⟩
  exact he.trans (congrArg (fun R : Raw w => R.opB a m) hd.2).symm

end WaveTurbulence.Reg.Skeleton
