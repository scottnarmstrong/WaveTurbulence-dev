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

end WaveTurbulence.LFTwist
