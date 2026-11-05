/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleErasureCoherence

/-! # Erase exactly the two coherent LF exceptions, retaining all core layers -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)

/-- The chosen couple alone stays coherent after erasing a native regular tree.
No coherence of unrelated attachments is assumed. -/
theorem eraseTree_couple_coherent (b : GBranch S.tree) (q : SourcePair S)
    (hc : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    CohOn (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b))
      (((D.eraseTree b).couple q).linksAt
        (inflatedPosition S (D.eraseTree b).tree (q.firstLeaf hS).toNode)
        (inflatedPosition S (D.eraseTree b).tree (q.secondLeaf hS).toNode)) := by
  rw [eraseTree_couple_links D hS b q] at hc
  exact (cohOn_map_iff _ _ _ (eraseTree_native_layerAt LG D hS hd b) _).mp hc

theorem CanonicalObject.eraseTree_coherent {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (b : GBranch S.tree)
    (ht : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))) :
    CanonicalObject p kind (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentTree_canonG _ D hS hd hc b ht)
  | couple hc => exact .couple (eraseCoherentTree_canonC _ D hS hd hc b ht)

theorem CanonicalObject.eraseCouple_coherent {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (q : SourcePair S)
    (hq : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    CanonicalObject p kind (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentCouple_canonG _ D hS hd hc q hq)
  | couple hc => exact .couple (eraseCoherentCouple_canonC _ D hS hd hc q hq)

/-- The actual source normalization erases just the lower tree and exceptional
couple, preserves the canonical kind and every induced core layer, and leaves
all other attachment codes unchanged. Already-trivial couples are skipped. -/
theorem normalize_exceptional_exists {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (b : GBranch S.tree) (q : SourcePair S)
    (ht : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)))
    (hq : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ E.tree b = .nil ∧ E.couple q = .triv ∧
      (∀ c, c ≠ b → E.tree c = D.tree c) ∧
      (∀ r, r ≠ q → E.couple r = D.couple r) ∧
      inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  let T := collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)
  let F := D.eraseTree b
  have hf : F.Decodes hS T.garden := eraseTree_collapse_decodes D hS hd b
  have hcan : CanonicalObject p kind T := hc.eraseTree_coherent LG D hS hd b ht
  have hcoh := eraseTree_couple_coherent LG D hS hd b q hq
  have hpre := eraseTree_inducedPrelayer_eq LG D hS hd b
  by_cases htriv : F.couple q = .triv
  · exact ⟨F,T,hf,hcan,D.eraseTree_at b,htriv,
      (fun c hc => D.eraseTree_other b c hc),(fun _ _ => rfl),hpre⟩
  · let C := collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hf q) p
    let E := F.eraseCouple q
    have he : E.Decodes hS C.garden := F.eraseCouple_collapse_decodes hS hf q htriv
    have hcan' : CanonicalObject p kind C := hcan.eraseCouple_coherent T F hS hf q hcoh
    refine ⟨E,C,he,hcan',D.eraseTree_at b,F.eraseCouple_at q,?_,?_,?_⟩
    · intro c hc
      exact D.eraseTree_other b c hc
    · intro r hr
      exact F.eraseCouple_other q r hr
    · exact (eraseCouple_inducedPrelayer_eq T F hS hf q htriv p).trans hpre

end WaveTurbulence.LFTwist
