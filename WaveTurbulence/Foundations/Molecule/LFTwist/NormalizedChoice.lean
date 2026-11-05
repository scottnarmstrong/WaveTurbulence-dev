/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExceptionalNormalization
public import WaveTurbulence.Foundations.Molecule.LFTwist.DecodedUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.SourceExpandedUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionChoice

/-! # Both literal normalized skeleton choices for a source LF operation -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (P : CorePlacement S)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG)
    (ht : CohOn LG ((D.tree P.lower).linksAt (nodeSign S.sig P.lower.1)
      (inflatedPosition S D.tree P.lower.toNode)))
    (hq : CohOn LG ((D.couple (pairOfLeaf S hS P.retained)).linksAt
      (inflatedPosition S D.tree ((pairOfLeaf S hS P.retained).firstLeaf hS).toNode)
      (inflatedPosition S D.tree ((pairOfLeaf S hS P.retained).secondLeaf hS).toNode)))
    {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible LG D hS hd P X B a)

@[expose] noncomputable def normalizedChoiceData (ε : Bool) : ReconstructionData (chosenSkeleton S P ε) :=
  transportReconstruction hS (chosenSkeleton_plain S P hS ε)
    (chosenBranchEquiv S P ε) (chosenLeafEquiv S P ε) (chosenLeafEquiv_pair S P ε)
    (normalizedData D P.lower (pairOfLeaf S hS P.retained))

include helig in
theorem normalization_eligible :
    SourceLayerEligible (normalizedLayered LG D hS hd P.lower (pairOfLeaf S hS P.retained) p)
      (normalizedData D P.lower (pairOfLeaf S hS P.retained)) hS
      (normalized_decodes LG D hS hd P.lower (pairOfLeaf S hS P.retained) p) P X B a := by
  unfold SourceLayerEligible at helig ⊢
  rw [normalized_inducedPrelayer LG D hS hd P.lower (pairOfLeaf S hS P.retained) p]
  exact helig

include hc ht hq hcore hP helig in
theorem normalization_sameLower :
    SameLowerLayer (normalizedLayered LG D hS hd P.lower (pairOfLeaf S hS P.retained) p)
      (expandedPlacement (normalizedData D P.lower (pairOfLeaf S hS P.retained)) hS
        (normalized_decodes LG D hS hd P.lower (pairOfLeaf S hS P.retained) p) P
        ((D.eraseTree P.lower).eraseCouple_at (pairOfLeaf S hS P.retained))) :=
  sourceExpanded_sameLowerLayer _ _ hS _ P _
    (normalized_canonical LG D hS hd P.lower (pairOfLeaf S hS P.retained) hc ht hq).criterion
    hcore hP (normalization_eligible LG D hS hd P helig)

@[expose] noncomputable def normalizedChoiceLayered (ε : Bool) : LayeredGarden w :=
  match ε with
  | false => normalizedLayered LG D hS hd P.lower (pairOfLeaf S hS P.retained) p
  | true => unitLayerTwist
      (normalizedLayered LG D hS hd P.lower (pairOfLeaf S hS P.retained) p)
      (expandedPlacement (normalizedData D P.lower (pairOfLeaf S hS P.retained)) hS
        (normalized_decodes LG D hS hd P.lower (pairOfLeaf S hS P.retained) p) P
        ((D.eraseTree P.lower).eraseCouple_at (pairOfLeaf S hS P.retained)))
      (normalization_sameLower LG D hS hd P hc ht hq hcore hP helig)

/-- Actual reconstruction data is retained for either choice, enabling subsequent LF steps. -/
theorem normalizedChoice_decodes (ε : Bool) :
    (normalizedChoiceData D hS P ε).Decodes (chosenSkeleton_plain S P hS ε)
      (normalizedChoiceLayered LG D hS hd P hc ht hq hcore hP helig ε).garden := by
  cases ε
  · have he : normalizedChoiceData D hS P false = normalizedData D P.lower (pairOfLeaf S hS P.retained) := by
      apply ReconstructionData.ext_tree_couple
      · funext b
        rfl
      · funext q
        let e := sourcePairEquiv hS hS (Equiv.refl _) (fun _ => rfl)
        have heq : e q = q := pairOfLeaf_firstLeaf S hS q
        apply congrArg (normalizedData D P.lower (pairOfLeaf S hS P.retained)).couple
        apply e.injective
        exact (e.apply_symm_apply q).trans heq.symm
    rw [he]
    exact normalized_decodes LG D hS hd P.lower (pairOfLeaf S hS P.retained) p
  · exact decoded_unit_decodes _ hS (normalized_decodes LG D hS hd P.lower (pairOfLeaf S hS P.retained) p)
      P (D.eraseTree_at P.lower) ((D.eraseTree P.lower).eraseCouple_at (pairOfLeaf S hS P.retained))

private theorem CanonicalObject.sourceUnit {u : ℕ} {T : Garden u} {H : LayeredGarden u}
    {F : ReconstructionData T} {hT : T.IsPlain} {hf : F.Decodes hT H.garden}
    {R : CorePlacement T} {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind H)
    (hq : F.couple (pairOfLeaf T hT R.retained) = .triv)
    {Y : VineType} {C : Finset (GBranch T.tree)} {c : GBranch T.tree}
    (hcore : IsCoreCLVine T Y C c R.lower) (hR : IsPlacementAt T C R.lower R)
    (helig : SourceLayerEligible H F hT hf R Y C c) :
    CanonicalObject p kind (unitLayerTwist H (expandedPlacement F hT hf R hq)
      (sourceExpanded_sameLowerLayer H F hT hf R hq hc.criterion hcore hR helig)) := by
  cases hc with
  | garden hc => exact .garden (sourceExpanded_unit_isCanonG _ F hT hf R hq hc hcore hR helig)
  | couple hc => exact .couple (sourceExpanded_unit_isCanonC _ F hT hf R hq hc hcore hR helig)

/-- Both source choices are canonical; no output canonicity is assumed. -/
theorem normalizedChoice_canonical (ε : Bool) :
    CanonicalObject p kind (normalizedChoiceLayered LG D hS hd P hc ht hq hcore hP helig ε) := by
  cases ε
  · exact normalized_canonical LG D hS hd P.lower (pairOfLeaf S hS P.retained) hc ht hq
  · exact (normalized_canonical LG D hS hd P.lower (pairOfLeaf S hS P.retained) hc ht hq).sourceUnit
      ((D.eraseTree P.lower).eraseCouple_at (pairOfLeaf S hS P.retained)) hcore hP
      (normalization_eligible LG D hS hd P helig)

/-- The optional unit preserves every normalized top-tree count. -/
theorem normalizedChoice_topOrder (ε : Bool) (j : Fin w) :
    (normalizedChoiceLayered LG D hS hd P hc ht hq hcore hP helig ε).topOrder p j =
      (normalizedLayered LG D hS hd P.lower (pairOfLeaf S hS P.retained) p).topOrder p j := by
  cases ε
  · rfl
  · exact unitLayerTwist_topOrder _ _ (normalization_sameLower LG D hS hd P hc ht hq hcore hP helig)
      (sourceExpanded_same_tree _ _ hS _ P _ hcore hP) p j

end WaveTurbulence.LFTwist
