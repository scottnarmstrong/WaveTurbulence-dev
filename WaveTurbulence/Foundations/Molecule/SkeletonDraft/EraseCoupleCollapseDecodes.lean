/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleCollapsePairsExact
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleCollapseForestExact

/-! # The literal source collapse of a nontrivial couple slot decodes its erased assignment -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_collapse_decodes {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) (p : SourcePair S)
    (hQ : D.couple p ≠ .triv) :
    (D.eraseCouple p).Decodes hS
      (collapseCoupleGarden (D.decoded_couple_isSubCouple hS hd p)) := by
  classical
  let E := D.eraseCouple p
  let A := inflatedPosition S D.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S D.tree (p.secondLeaf hS).toNode
  let a := D.decodedNode hS hd (p.firstLeaf hS).toNode
  let h := D.decoded_couple_isSubCouple hS hd p
  let H := collapseCoupleGarden h
  have ha : nodeSign G.sig a.1 = 1 :=
    (D.decodedNode_sign hS hd _).trans (sourcePair_first_sign S hS p)
  have hp : sourcePairs H = E.attachmentPairs hS := by
    have hr := collapseCoupleGarden_root_pair h ha
    have he := D.eraseCouple_collapse_pairs_erase hS hd p hQ
    have hblock : E.couplePairBlock hS p = {(A,B)} := by
      change ((E.couple p).pairsAt _ _).toFinset = _
      rw [D.eraseCouple_at]
      rfl
    calc
      sourcePairs H = (sourcePairs H).erase (A,B) ∪ {(A,B)} :=
        (Finset.erase_union_eq (A,B) (sourcePairs H) hr).symm
      _ = D.coupleBackground hS p ∪ {(A,B)} := congrArg (fun X => X ∪ {(A,B)}) he
      _ = E.coupleBackground hS p ∪ E.couplePairBlock hS p :=
        congrArg₂ (fun X Y => X ∪ Y) (D.eraseCouple_background hS p).symm hblock.symm
      _ = E.attachmentPairs hS := (E.attachmentPairs_eq_background_union hS p).symm
  refine ⟨collapseCoupleGarden_plain h hd.1,?_⟩
  apply Raw.ext
  · have hs := congrArg Raw.sig hd.2
    exact hs
  · exact (D.eraseCouple_collapse_tree hS hd p).symm
  · exact hp.symm

end WaveTurbulence.Reg.Skeleton
