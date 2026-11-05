/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CoherentInsertion
public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleCollapseCanonical

/-! # Coherent collapse is realized by the literal reverse insertion

These are the insertion witnesses needed to realize the identity LF operation;
source patterns on unchanged coherent attachments are derived from canonicity.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} (LG : LayeredGarden w)

/-- Reinsert exactly the coherent regular tree that was actually collapsed. -/
theorem reinsert_collapsed_tree {a b : GNode LG.garden.tree}
    (h : Comb.IsSubPairedTree LG.garden a b) {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (X : RegChain) (ζ : ℤˣ)
    (hwf : X.wf = true) (hs : nodeSign LG.garden.sig a.1 = ζ)
    (hE : ChainEmb LG.garden X ζ a.1 (Comb.nodeSubtree b))
    (hcoh : CohOn LG (X.linksAt ζ a.1)) (hb : b.1 = addrExt a.1 X.lonePath) :
    CoherentTreeInsertion p (collapsePairedTreeLayered LG h) LG a.1 ζ (Comb.nodeSubtree b) X := by
  have hA : OutAgreeT LG (collapsePairedTreeLayered LG h) a.1
      (addrExt a.1 X.lonePath) (addrExt a.1 RegChain.nil.lonePath) := by
    simpa only [← hb,RegChain.lonePath,addrExt_nil] using collapsePairedTree_outAgree LG h
  exact ⟨hwf,rfl,hs,collapsePairedTree_embeds_nil LG h ζ,hE,hA.symm hE,
    treePattern_of_canon hc.criterion hc.plain hwf hE hcoh⟩

/-- Reinsert exactly the coherent regular couple that was actually collapsed. -/
theorem reinsert_collapsed_couple {a b : GNode LG.garden.tree}
    (h : Comb.IsSubCouple LG.garden a b) {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind LG) (Q : RegCpl) (hwf : Q.wf = true)
    (ha : nodeSign LG.garden.sig a.1 = 1) (hb : nodeSign LG.garden.sig b.1 = -1)
    (hE : Embeds LG.garden Q a.1 b.1) (hcoh : CohOn LG (Q.linksAt a.1 b.1)) :
    CoherentCoupleInsertion p (collapseCoupleLayered LG h p) LG a.1 b.1 Q :=
  ⟨hwf,rfl,ha,hb,collapseCouple_embeds_triv LG h hE.indep,hE,
    (collapseCouple_outAgree LG h p hc.criterion hc.plain).symm,
    layerPattern_of_canon hc.criterion hc.plain hwf hE hcoh⟩

/-- Literal outside agreement includes the identity operation. -/
theorem outAgree_refl (a b : Address w) : OutAgree LG LG a b := by
  constructor
  · intro _ _
    rfl
  · intro _ _
    rfl
  · intro _ _
    rfl
  · intro l m _ he
    exact congrArg (fun l : GLeaf LG.garden.tree => (LG.garden.pair l).1) (Subtype.ext he)

/-- An already trivial coherent couple is an allowed unchanged reinsertion. -/
theorem reinsert_triv_identity {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG)
    (a b : Address w) (ha : nodeSign LG.garden.sig a = 1) (hb : nodeSign LG.garden.sig b = -1)
    (hE : Embeds LG.garden .triv a b) : CoherentCoupleInsertion p LG LG a b .triv := by
  have hcoh : CohOn LG (RegCpl.triv.linksAt a b) := by
    simp only [CohOn,RegCpl.linksAt,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  exact ⟨rfl,rfl,ha,hb,hE,hE,outAgree_refl LG a b,
    layerPattern_of_canon hc.criterion hc.plain rfl hE hcoh⟩

end WaveTurbulence.LFTwist
