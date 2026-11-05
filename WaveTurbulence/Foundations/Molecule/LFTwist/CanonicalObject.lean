/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureCoherence

/-! # A source-class index for the two canonical object kinds

This records the original G/C kind so that finite coherent-erasure arguments
preserve both classes without assuming an abstract canonicity-closure axiom.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

inductive CanonicalObject (p : ℕ) : Bool → {w : ℕ} → LayeredGarden w → Prop
  | garden {w : ℕ} {LG : LayeredGarden w} (hc : IsCanonG (p+1) LG) : CanonicalObject p true LG
  | couple {LG : LayeredGarden 2} (hc : IsCanonC (p+1) LG) : CanonicalObject p false LG

theorem CanonicalObject.criterion {p : ℕ} {kind : Bool} {w : ℕ} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) : LG.CanonCriterion p := by
  cases hc with
  | garden hc => exact hc.2.2.2
  | couple hc => exact hc.2

theorem CanonicalObject.plain {p : ℕ} {kind : Bool} {w : ℕ} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) : LG.garden.IsPlain := by
  cases hc with
  | garden hc => exact hc.2.1
  | couple hc => exact hc.1.1

theorem CanonicalObject.eraseTree {p : ℕ} {kind : Bool} {w : ℕ} {S : Garden w} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (hall : AllAttachmentsCoherent LG D hS) (b : GBranch S.tree) :
    CanonicalObject p kind (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentTree_canonG LG D hS hd hc b (hall.1 b))
  | couple hc => exact .couple (eraseCoherentTree_canonC _ D hS hd hc b (hall.1 b))

theorem CanonicalObject.eraseCouple {p : ℕ} {kind : Bool} {w : ℕ} {S : Garden w} {LG : LayeredGarden w}
    (hc : CanonicalObject p kind LG) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (hall : AllAttachmentsCoherent LG D hS) (q : SourcePair S) :
    CanonicalObject p kind (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p) := by
  cases hc with
  | garden hc => exact .garden (eraseCoherentCouple_canonG LG D hS hd hc q (hall.2 q))
  | couple hc => exact .couple (eraseCoherentCouple_canonC _ D hS hd hc q (hall.2 q))

end WaveTurbulence.LFTwist
