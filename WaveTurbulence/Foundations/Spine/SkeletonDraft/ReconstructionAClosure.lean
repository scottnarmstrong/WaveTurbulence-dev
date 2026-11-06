/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionSubstitutePairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawCoupleInsertion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawValidityFaithfulness

/-! # Source A expansion preserves the range of actual regular reconstruction assignments -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.substitutePair_decodes {w : ℕ} {S G H : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
    (x y : Address w) (Q : RegCpl) (hH : H.IsPlain)
    (hp : (x,y) ∈ sourcePairs G)
    (he : rawOfGarden H = (rawOfGarden G).insertCouple x y Q) :
    (D.substitutePair hS x y Q).Decodes hS H := by
  let E := D.substitutePair hS x y Q
  have hpD : (x,y) ∈ D.attachmentPairs hS := by
    have he := congrArg Raw.pairs hd.2
    change D.attachmentPairs hS = sourcePairs G at he
    exact he.symm ▸ hp
  have hpair := D.substitutePair_pairs hS x y Q hpD
  have hrawpairs : (E.raw hS).pairs = (rawOfGarden H).pairs :=
    hpair.trans ((congrArg (fun R : Raw w => (R.insertCouple x y Q).pairs) hd.2).trans
      (congrArg Raw.pairs he).symm)
  have hs : (E.raw hS).sig = (rawOfGarden H).sig := by
    have hG := congrArg Raw.sig hd.2
    have hH := congrArg Raw.sig he
    exact hG.trans hH.symm
  exact ⟨hH,Raw.eq_of_valid_sig_pairs _ _ (E.raw_valid hS) (rawOfGarden_valid H hH) hs hrawpairs⟩

theorem ReconstructionData.opA_decodes {w : ℕ} {S G H : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
    (x y : Address w) (k : MiniCplCode) (hH : H.IsPlain)
    (hp : (x,y) ∈ sourcePairs G) (he : rawOfGarden H = (rawOfGarden G).opA x y k) :
    ∃ E : ReconstructionData S, E.Decodes hS H := by
  refine ⟨D.substitutePair hS x y (miniCoupleCode k),?_⟩
  apply D.substitutePair_decodes hS hd x y (miniCoupleCode k) hH hp
  exact he.trans ((rawOfGarden G).insertCouple_mini x y k).symm

end WaveTurbulence.Reg.Skeleton
