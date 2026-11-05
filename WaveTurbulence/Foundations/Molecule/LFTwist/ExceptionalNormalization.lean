/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NormalizeExceptional

/-! # The explicit two-exception normalization used in the LF construction -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) (q : SourcePair S)

@[expose] noncomputable def normalizedData : ReconstructionData S := (D.eraseTree b).eraseCouple q

@[expose] noncomputable def normalizedLayered (p : ℕ) : LayeredGarden w := by
  classical
  exact
  let T := collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)
  if D.couple q = .triv then T else
    collapseCoupleLayered T ((D.eraseTree b).decoded_couple_isSubCouple hS
      (eraseTree_collapse_decodes D hS hd b) q) p

/-- The explicit normalization is decoded by exactly the two erased codes. -/
theorem normalized_decodes (p : ℕ) :
    (normalizedData D b q).Decodes hS (normalizedLayered LG D hS hd b q p).garden := by
  by_cases hq : D.couple q = .triv
  · have hf : (D.eraseTree b).couple q = .triv := hq
    have he := (D.eraseTree b).eraseCouple_eq_self q hf
    unfold normalizedLayered
    dsimp only
    rw [if_pos hq]
    change ((D.eraseTree b).eraseCouple q).Decodes hS (collapsePairedTreeGarden _)
    rw [he]
    exact eraseTree_collapse_decodes D hS hd b
  · have hf : (D.eraseTree b).couple q ≠ .triv := hq
    unfold normalizedLayered
    dsimp only
    rw [if_neg hq]
    exact (D.eraseTree b).eraseCouple_collapse_decodes hS (eraseTree_collapse_decodes D hS hd b) q hf

theorem normalized_canonical {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG)
    (ht : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)))
    (hq : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    CanonicalObject p kind (normalizedLayered LG D hS hd b q p) := by
  have hcan := hc.eraseTree_coherent LG D hS hd b ht
  unfold normalizedLayered
  dsimp only
  split
  · exact hcan
  · exact hcan.eraseCouple_coherent _ (D.eraseTree b) hS (eraseTree_collapse_decodes D hS hd b) q
      (eraseTree_couple_coherent LG D hS hd b q hq)

private theorem prelayer_congr {A B : LayeredGarden w} {F E : ReconstructionData S}
    (hg : A = B) (he : F = E) (ha : F.Decodes hS A.garden) (hb : E.Decodes hS B.garden) :
    inducedPrelayer A F hS ha = inducedPrelayer B E hS hb := by
  subst B
  subst E
  rfl

/-- No original branching layer changes during the explicit normalization. -/
theorem normalized_inducedPrelayer (p : ℕ) :
    inducedPrelayer (normalizedLayered LG D hS hd b q p) (normalizedData D b q) hS
      (normalized_decodes LG D hS hd b q p) = inducedPrelayer LG D hS hd := by
  by_cases hq : D.couple q = .triv
  · have hf : (D.eraseTree b).couple q = .triv := hq
    have he := (D.eraseTree b).eraseCouple_eq_self q hf
    have hg : normalizedLayered LG D hS hd b q p =
        collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b) := by
      simp only [normalizedLayered,hq,ite_true]
    exact (prelayer_congr hS hg he (normalized_decodes LG D hS hd b q p)
      (eraseTree_collapse_decodes D hS hd b)).trans (eraseTree_inducedPrelayer_eq LG D hS hd b)
  · have hg : normalizedLayered LG D hS hd b q p =
        collapseCoupleLayered (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b))
          ((D.eraseTree b).decoded_couple_isSubCouple hS (eraseTree_collapse_decodes D hS hd b) q) p := by
      simp only [normalizedLayered,hq,ite_false]
    exact (prelayer_congr hS hg rfl (normalized_decodes LG D hS hd b q p)
      ((D.eraseTree b).eraseCouple_collapse_decodes hS (eraseTree_collapse_decodes D hS hd b) q hq)).trans
      ((eraseCouple_inducedPrelayer_eq _ (D.eraseTree b) hS
        (eraseTree_collapse_decodes D hS hd b) q hq p).trans (eraseTree_inducedPrelayer_eq LG D hS hd b))

end WaveTurbulence.LFTwist
