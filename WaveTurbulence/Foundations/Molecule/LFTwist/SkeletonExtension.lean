/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.EraseAllTrees
public import WaveTurbulence.Foundations.Molecule.LFTwist.EraseAllCouples

/-! # TARGET sublayer: existence and uniqueness of the canonical skeleton extension

All coherent native trees are erased first, then all coherent couples.
Every step keeps the induced branch pre-layering. Identity reconstruction
is the literal source garden; its canonical leaf layers are the minimum
parent layers, so the explicit extension is canonical and unique.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

theorem CanonicalObject.isCanonG {p w : ℕ} {LG : LayeredGarden w}
    (hc : CanonicalObject p true LG) : IsCanonG (p+1) LG := by
  cases hc with
  | garden hc => exact hc

theorem CanonicalObject.isCanonC {p : ℕ} {LG : LayeredGarden 2}
    (hc : CanonicalObject p false LG) : IsCanonC (p+1) LG := by
  cases hc with
  | couple hc => exact hc

/-- The explicit skeleton layering keeps inherited branch layers and uses the
minimum-parent rule at each actual source leaf pair. -/
@[expose] noncomputable def inducedSkeleton {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (p : ℕ) : LayeredGarden w :=
  branchLayeredGarden S (inducedPrelayer LG D hS hd) p (inducedPrelayer_isBranchPrelayering LG D hS hd)

theorem inducedSkeleton_branch {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (p : ℕ) (b : GBranch S.tree) :
    (inducedSkeleton LG D hS hd p).layer b.toNode = inducedPrelayer LG D hS hd b :=
  extendBranchLayers_branch _ _ _ _

private theorem canonical_extension_of_identity {w : ℕ} {S : Garden w} (hS : S.IsPlain)
    {p : ℕ} {kind : Bool} (LH : LayeredGarden w)
    (hd : (ReconstructionData.identity S).Decodes hS LH.garden) (hc : CanonicalObject p kind LH)
    (f : GBranch S.tree → ℕ) (hf : IsBranchPrelayering S f)
    (hlabels : f = inducedPrelayer LH (ReconstructionData.identity S) hS hd) :
    CanonicalObject p kind (branchLayeredGarden S f p hf) := by
  have hG : LH.garden = S := rawOfGarden_injective_plain hd.1 hS
    (hd.2.symm.trans (ReconstructionData.identity_raw S hS))
  cases LH with
  | mk G layer hL =>
    change G = S at hG
    subst G
    have hcore : inducedPrelayer ⟨S,layer,hL⟩ (ReconstructionData.identity S) hS hd =
        (fun b : GBranch S.tree => layer b.toNode) := by
      funext b
      apply congrArg layer
      exact Subtype.ext (nilTrees_corePosition (ReconstructionData.identity S) (fun _ => rfl) b)
    have hext : extendBranchLayers S f p = layer :=
      (congrArg (fun g => extendBranchLayers S g p) (hlabels.trans hcore)).trans
        (extendBranchLayers_eq_canonical ⟨S,layer,hL⟩ p hc.criterion hc.plain)
    have hObj : branchLayeredGarden S f p hf = (⟨S,layer,hL⟩ : LayeredGarden w) := by
      change LayeredGarden.mk S (extendBranchLayers S f p) _ = LayeredGarden.mk S layer hL
      cases hext
      rfl
    exact hObj.symm ▸ hc

/-- TARGET Remark sublayer: all-coherent reconstruction induces a canonical
skeleton layering, for either source canonical object kind. -/
theorem coherent_inducedSkeleton_canonical {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG) (hall : AllAttachmentsCoherent LG D hS) :
    CanonicalObject p kind (inducedSkeleton LG D hS hd p) := by
  obtain ⟨E,LH,he,hc',hall',hn,hcpl,hcore⟩ := eraseAllTrees hS LG D hd hc hall
  obtain ⟨F,LK,hf,hc'',hF,hcore'⟩ := eraseAllCouples hS LH E he hc' hall' hn
  have hlabels := hcore'.trans hcore
  subst F
  exact canonical_extension_of_identity hS LK hf hc'' (inducedPrelayer LG D hS hd)
    (inducedPrelayer_isBranchPrelayering LG D hS hd) hlabels.symm

/-- Canonical garden version of TARGET sublayer. -/
theorem coherent_inducedSkeleton_isCanonG {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonG (p+1) LG) (hall : AllAttachmentsCoherent LG D hS) :
    IsCanonG (p+1) (inducedSkeleton LG D hS hd p) :=
  (coherent_inducedSkeleton_canonical LG D hS hd (.garden hc) hall).isCanonG

/-- Canonical couple version of TARGET sublayer. -/
theorem coherent_inducedSkeleton_isCanonC {S : Garden 2} (LG : LayeredGarden 2)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonC (p+1) LG) (hall : AllAttachmentsCoherent LG D hS) :
    IsCanonC (p+1) (inducedSkeleton LG D hS hd p) :=
  (coherent_inducedSkeleton_canonical LG D hS hd (.couple hc) hall).isCanonC

/-- The canonical extension of the inherited branch pre-layering is unique. -/
theorem coherent_inducedSkeleton_unique {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG) (hall : AllAttachmentsCoherent LG D hS)
    (f : GNode S.tree → ℕ) (hL : IsLayering S f) (hcan : (LayeredGarden.mk S f hL).CanonCriterion p)
    (hb : ∀ b : GBranch S.tree, f b.toNode = inducedPrelayer LG D hS hd b) :
    f = (inducedSkeleton LG D hS hd p).layer := by
  exact canonical_layer_unique S f (inducedSkeleton LG D hS hd p).layer hL
    (inducedSkeleton LG D hS hd p).isLayering hS p hcan
    (coherent_inducedSkeleton_canonical LG D hS hd hc hall).criterion
    (fun b => (hb b).trans (inducedSkeleton_branch LG D hS hd p b).symm)

end WaveTurbulence.LFTwist
