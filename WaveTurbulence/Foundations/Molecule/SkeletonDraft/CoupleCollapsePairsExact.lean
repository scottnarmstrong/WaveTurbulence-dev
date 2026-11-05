/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleBackgroundOutside
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleBlockBelow
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsedCouplePairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionRegularCouples

/-! # Exact surviving matching after collapse of one nontrivial couple replacement -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_collapse_pairs_erase {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) (p : SourcePair S)
    (hQ : D.couple p ≠ .triv) :
    let A := inflatedPosition S D.tree (p.firstLeaf hS).toNode
    let B := inflatedPosition S D.tree (p.secondLeaf hS).toNode
    (sourcePairs (collapseCoupleGarden (D.decoded_couple_isSubCouple hS hd p))).erase (A,B) =
      D.coupleBackground hS p := by
  classical
  let a := D.decodedNode hS hd (p.firstLeaf hS).toNode
  let b := D.decodedNode hS hd (p.secondLeaf hS).toNode
  let h := D.decoded_couple_isSubCouple hS hd p
  have ha : nodeSign G.sig a.1 = 1 :=
    (D.decodedNode_sign hS hd _).trans (sourcePair_first_sign S hS p)
  have hp := collapseCoupleGarden_pairs_erase h ha
  have hraw := congrArg Raw.pairs hd.2
  change D.attachmentPairs hS = sourcePairs G at hraw
  rw [← hraw,D.attachmentPairs_eq_background_union hS p] at hp
  exact hp.trans (by
    ext q
    constructor
    · intro hq
      obtain ⟨hq,z,hz⟩ := Finset.mem_filter.mp hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hq
      · have hbelow := couple_pair_first_below (D.couple p) _ _ q (List.mem_toFinset.mp hq)
        rcases hbelow with hl | hr
        · exact (z.2.1 (hz.symm ▸ hl)).elim
        · exact (z.2.2 (hz.symm ▸ hr)).elim
    · intro hq
      have hm : q ∈ sourcePairs G := hraw ▸ (by
        rw [D.attachmentPairs_eq_background_union hS p]
        exact Finset.mem_union_left _ hq)
      have hv := (rawOfGarden_valid G hd.1).1 q hm
      let ℓ : GLeaf G.tree := ⟨q.1,hv.1⟩
      have hout := D.coupleBackground_not_below hS p hQ q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hq,⟨ℓ,hout⟩,rfl⟩)

end WaveTurbulence.Reg.Skeleton
