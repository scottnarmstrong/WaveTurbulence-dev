/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTopLayer
/-! Eligibility of coherent regular objects: TARGET L899–905 and L951.
The ambient canonical garden is retained explicitly. Coherence alone does not authorize
applying the coherent estimates to an arbitrary layered object. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Links WaveTurbulence.Reg TTree

/-- TARGET L899: an embedded coherent regular couple, with parent layers q and q'.
The local layering is the restriction of the ambient layering along its two root addresses. -/
def IsCoherentCoupleAt (p q q' : ℕ) (Q : RegCpl) (LG : LayeredGarden 2) : Prop :=
  Q.wf = true ∧ Q.Decodes LG.garden ∧
    ∃ (w : ℕ) (H : LayeredGarden w) (a b : Fin w × Path),
      IsCanonGC (p + 1) H ∧ Embeds H.garden Q a b ∧
      nodeSign H.garden.sig a = 1 ∧ nodeSign H.garden.sig b = -1 ∧
      CohOn H (Q.linksAt a b) ∧ parAt H p a = q ∧ parAt H p b = q' ∧
      ∀ z : GNode LG.garden.tree,
        LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)

/-- TARGET L901: an embedded coherent regular tree, with root parent layer q and lone-leaf
layer q'. The subtree inserted at the lone leaf is part of the ambient embedding data. -/
def IsCoherentTreeAt (p q q' : ℕ) (X : RegChain) (LG : LayeredGarden 1) : Prop :=
  X.wf = true ∧ X.DecodesTree LG.garden ∧
    ∃ (w : ℕ) (H : LayeredGarden w) (a : Fin w × Path) (h : TTree),
      IsCanonGC (p + 1) H ∧ ChainEmb H.garden X (LG.garden.sig 0) a h ∧
      nodeSign H.garden.sig a = LG.garden.sig 0 ∧
      CohOn H (X.linksAt (LG.garden.sig 0) a) ∧ parAt H p a = q ∧
      layerAt H (addrExt a X.lonePath) = q' ∧
      ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)

/-- A whole coherent canonical couple is an eligible object with both parent layers p. -/
theorem isCoherentCoupleAt_of_canonical {p : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hcan : IsCanonC (p + 1) LG) (hwf : Q.wf = true)
    (hQ : Q.Decodes LG.garden) (hcoh : LG.incoherency Q.links = 0) :
    IsCoherentCoupleAt p p p Q LG := by
  refine ⟨hwf, hQ, 2, LG, (0, []), (1, []), ?_, Embeds.of_decodes hQ,
    ?_, ?_, (coherent_iff hQ).1 hcoh, parAt_root LG p 0, parAt_root LG p 1, ?_⟩
  · exact (Canon.isCanonGC_iff_isCanonC _ _).2 hcan
  · simp [nodeSign, TTree.pathSign, hQ.1.2]
  · simp [nodeSign, TTree.pathSign, hQ.1.2]
  · intro z
    have he : addrExt (if z.1.1 = 0 then (0, []) else (1, [])) z.1.2 = z.1 := by
      rcases z with ⟨⟨i, path⟩, hi⟩
      fin_cases i <;> simp [addrExt]
    rw [he, layerAt_node]

end WaveTurbulence.LGSpine
