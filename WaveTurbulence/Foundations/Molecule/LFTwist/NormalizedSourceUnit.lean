/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NormalizeExceptional
public import WaveTurbulence.Foundations.Molecule.LFTwist.DecodedUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.SourceExpandedUnit

/-! # Source-eligible normalization and the optional canonical reconstructed unit -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (P : CorePlacement S)

private theorem canonicalObject_unit {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    CanonicalObject p kind (unitLayerTwist LG (expandedPlacement D hS hd P hq)
      (sourceExpanded_sameLowerLayer LG D hS hd P hq hc.criterion hcore hP helig)) := by
  cases hc with
  | garden hc => exact .garden (sourceExpanded_unit_isCanonG _ D hS hd P hq hc hcore hP helig)
  | couple hc => exact .couple (sourceExpanded_unit_isCanonC _ D hS hd P hq hc hcore hP helig)

/-- Starting from an arbitrary canonical source garden, erase exactly its two
coherent exceptional objects and perform the eligible actual unit twist.
Both outputs are canonical and the second is decoded by the actual transported
assignment. Coherence of unrelated attachments is unnecessary. -/
theorem normalized_source_unit_exists {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG)
    (ht : CohOn LG ((D.tree P.lower).linksAt (nodeSign S.sig P.lower.1)
      (inflatedPosition S D.tree P.lower.toNode)))
    (hq : CohOn LG ((D.couple (pairOfLeaf S hS P.retained)).linksAt
      (inflatedPosition S D.tree ((pairOfLeaf S hS P.retained).firstLeaf hS).toNode)
      (inflatedPosition S D.tree ((pairOfLeaf S hS P.retained).secondLeaf hS).toNode)))
    {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a) :
    ∃ (E : ReconstructionData S) (H H' : LayeredGarden w) (he : E.Decodes hS H.garden),
      CanonicalObject p kind H ∧ CanonicalObject p kind H' ∧
      E.tree P.lower = .nil ∧ E.couple (pairOfLeaf S hS P.retained) = .triv ∧
      (∀ b, b ≠ P.lower → E.tree b = D.tree b) ∧
      (∀ q, q ≠ pairOfLeaf S hS P.retained → E.couple q = D.couple q) ∧
      inducedPrelayer H E hS he = inducedPrelayer LG D hS hd ∧
      (twistReconstruction S P hS E).Decodes (unitTwistGarden_plain S P hS) H'.garden ∧
      H'.garden.order = H.garden.order ∧ (∀ j, H'.topOrder p j = H.topOrder p j) := by
  obtain ⟨E,H,he,hcan,hnil,htriv,hotherT,hotherQ,hpre⟩ :=
    normalize_exceptional_exists LG D hS hd hc P.lower (pairOfLeaf S hS P.retained) ht hq
  have helig' : SourceLayerEligible H E hS he P X B a := by
    unfold SourceLayerEligible at helig ⊢
    rw [hpre]
    exact helig
  let Q := expandedPlacement E hS he P htriv
  have heq : SameLowerLayer H Q := sourceExpanded_sameLowerLayer H E hS he P htriv
    hcan.criterion hcore hP helig'
  let H' := unitLayerTwist H Q heq
  refine ⟨E,H,H',he,hcan,canonicalObject_unit H E hS he P hcan htriv hcore hP helig',
    hnil,htriv,hotherT,hotherQ,hpre,decoded_unit_decodes E hS he P hnil htriv,
    unitLayerTwist_order H Q heq,?_⟩
  intro j
  exact unitLayerTwist_topOrder H Q heq (sourceExpanded_same_tree H E hS he P htriv hcore hP) p j

end WaveTurbulence.LFTwist
