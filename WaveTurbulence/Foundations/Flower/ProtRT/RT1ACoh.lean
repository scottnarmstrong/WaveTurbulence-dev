/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplOn
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2APre

/-! # RT-GATE (ii), shape (a+): the pieces in the windowed signed ambient

D3-HELPER's `tc2a_cohB/I/R/G` (ProtPin/TChild2ACoh.lean; copy recorded in RT1A.lean's header) with the windowed ambient
`MkSlotsO.CplAmbient p p q' Q LG` (the partner root `b` with parent layer `q'`): the rest couple, when coherent, is a
coherent couple with parent layers `𝔏_b` and `q'`; the interior and the side couples as before (they only read the
traced side). Also the partner root of the rest couple lies in a layer `≤ q'` (`rt1a_rootB1_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

/-- The partner root of the rest couple is the partner root of the traced couple. -/
theorem rt1a_rootB1_le {q' : ℕ} (hr : layerAt LG ((1 : Fin 2), []) ≤ q') :
    LGB.layer (GNode.root LGB.garden.tree 1) ≤ q' := by
  rw [D.layB]
  have e : botAddr (cpair m Qr Qg inner).lonePath (GNode.root LGB.garden.tree 1).1 = ((1 : Fin 2), []) := by
    simp [botAddr, GNode.root]
  rw [e]
  exact hr

/-- **The rest couple, when coherent**, is a coherent couple of the ambient, parents `𝔫_b` and `b` (layer `q'`). -/
theorem rt1a_cohB {p q' : ℕ} {rest Xm : RegChain} {Qlp : RegCpl}
    (hA : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
    (hwB : (SourceApp.closeCouple rest Xm Qlp).wf = true)
    (hdB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden)
    (h0 : LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links = 0) :
    IsCoherentCoupleAt p (layerAt LG ((0 : Fin 2), bPath m inner)) q' (SourceApp.closeCouple rest Xm Qlp) LGB := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, -, hpb, hlay⟩ := hA
  obtain ⟨hX, hY, hQ⟩ := hE.type2
  obtain ⟨-, -, -, hR⟩ := hX.parts
  rw [slotSign_lone] at hR
  have hlp := tc2a_lone_path D P
  have hQ' : Embeds H.garden Qlp (addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath)
      (addrExt b Xm.lonePath) := by
    rw [addrExt_append]
    simpa [RegChain.lonePath, List.append_assoc] using hQ
  have hind : Indep (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) b := by
    have := hE.indep.ext ([m.c] ++ inner.lonePath ++ [m.lone]) []
    rwa [show addrExt b ([] : TTree.Path) = b by simp [addrExt]] at this
  have hEB := tc2a_embeds_close hR hY hQ' hind
  have hl : ∀ z : GNode LGB.garden.tree, LGB.layer z = layerAt H
      (addrExt (if z.1.1 = 0 then addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) else b) z.1.2) := by
    intro z
    have hm := (D.gd.bot_iff z.1).1.2 z.2
    rw [D.layB z, layerAt_of_mem LG hm, hlay ⟨botAddr (cpair m Qr Qg inner).lonePath z.1, hm⟩]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [botAddr, hz, addrExt, hlp, List.append_assoc]
    · simp [botAddr, hz, addrExt]
  have hlb := (tc2a_amb_layers D P hlay).2
  refine ⟨hwB, hdB, w', H, _, _, hcan, hEB, ?_, hsb, cohOn_of_couple hdB hl h0, ?_, hpb, hl⟩
  · rw [show [m.c] ++ inner.lonePath ++ [m.lone] = (RegChain.pair m Qr Qg inner .nil).lonePath by
      simp [RegChain.lonePath], nodeSign_spine, hsa]
  · have e : addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]) = addrExt (addrExt a (bPath m inner)) [m.lone] := by
      rw [addrExt_append]; simp [bPath]
    rw [e, parAt_child H p m.lone (by rw [← e]; exact hEB.nodeA), hlb]

/-- **The interior, when coherent.** -/
theorem rt1a_cohI {p q' : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
    (hj : layerAt LG ((0 : Fin 2), []) = p) (hwI : inner.wf = true)
    (h0 : LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0) :
    IsCoherentTreeAt p p (layerAt LG ((0 : Fin 2), bPath m inner)) inner LGi := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, -, -, -, hlay⟩ := hA
  obtain ⟨hX, -, -⟩ := hE.type2
  obtain ⟨-, -, hI, -⟩ := hX.parts
  obtain ⟨hla, hlb⟩ := tc2a_amb_layers D P hlay
  have hsI : LGi.garden.sig 0 = slotSign 1 m.c := by rw [P.sigI, hsZ]
  have hl : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt H (addrExt (addrExt a [m.c]) z.1.2) := by
    intro z
    rw [← layerAt_node, tc2a_layI D P z.1 z.2, layerAt_of_mem LG (z := ((0 : Fin 2), m.c :: z.1.2)) (D.gd.ι₁ (P.hp.ιi z)).2,
      hlay ⟨((0 : Fin 2), m.c :: z.1.2), (D.gd.ι₁ (P.hp.ιi z)).2⟩]
    simp [addrExt]
  refine ⟨hwI, P.decI, w', H, addrExt a [m.c], _, hcan, by rw [hsI]; exact hI, ?_, cohOn_of_tree P.decI hl h0, ?_, ?_,
    hl⟩
  · rw [nodeSign_step, hsa, hsI]
  · rw [parAt_child H p m.c hI.node, hla, hj]
  · rw [addrExt_append, ← hlb]; rfl

/-- **The red side couple, when coherent.** -/
theorem rt1a_cohR {p q' : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
    (hwr : Qr.wf = true) (h0 : LGr.incoherency Qr.links = 0) :
    IsCoherentCoupleAt p
      (tc2aQR m inner (LGZ.garden.sig 0) (layerAt LG ((0 : Fin 2), [])) (layerAt LG ((0 : Fin 2), bPath m inner)) 0)
      (tc2aQR m inner (LGZ.garden.sig 0) (layerAt LG ((0 : Fin 2), [])) (layerAt LG ((0 : Fin 2), bPath m inner)) 1)
      Qr LGr := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, -, -, -, hlay⟩ := hA
  obtain ⟨hX, -, -⟩ := hE.type2
  obtain ⟨hr, -, -, -⟩ := hX.parts
  obtain ⟨hla, hlb⟩ := tc2a_amb_layers D P hlay
  have hl : ∀ z : GNode LGr.garden.tree, LGr.layer z =
      layerAt H (addrExt a (rBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2)) := by
    intro z
    rw [← layerAt_node, tc2a_layR D P z.1 z.2, layerAt_of_mem LG (z := ((0 : Fin 2), rBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2)) (D.gd.ι₁ (P.hp.ιr z)).2,
      hlay ⟨((0 : Fin 2), rBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2), (D.gd.ι₁ (P.hp.ιr z)).2⟩]
    simp [addrExt]
  unfold tc2aQR
  rw [hsZ] at hl ⊢
  exact tc2a_side_coh hcan hsa hwr P.decR (bPath m inner) m.red.1 m.red.2 (rBase m inner 1)
    (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs]⟩) (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs]⟩)
    (by simp [bPath]) (by rw [show bPath m inner ++ [m.red.2] = [m.c] ++ inner.lonePath ++ [m.red.2] by simp [bPath],
      nodeSign_chain_child, hsa, slotSign_red])
    (by simpa [bPath] using hr) hla hlb hl h0

/-- **The green side couple, when coherent.** -/
theorem rt1a_cohG {p q' : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
    (hwg : Qg.wf = true) (h0 : LGg.incoherency Qg.links = 0) :
    IsCoherentCoupleAt p
      (tc2aQG m inner (LGZ.garden.sig 0) (layerAt LG ((0 : Fin 2), [])) (layerAt LG ((0 : Fin 2), bPath m inner)) 0)
      (tc2aQG m inner (LGZ.garden.sig 0) (layerAt LG ((0 : Fin 2), [])) (layerAt LG ((0 : Fin 2), bPath m inner)) 1)
      Qg LGg := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, -, -, -, hlay⟩ := hA
  obtain ⟨hX, -, -⟩ := hE.type2
  obtain ⟨-, hg, -, -⟩ := hX.parts
  obtain ⟨hla, hlb⟩ := tc2a_amb_layers D P hlay
  have hl : ∀ z : GNode LGg.garden.tree, LGg.layer z =
      layerAt H (addrExt a (gBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2)) := by
    intro z
    rw [← layerAt_node, tc2a_layG D P z.1 z.2, layerAt_of_mem LG (z := ((0 : Fin 2), gBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2)) (D.gd.ι₁ (P.hp.ιg z)).2,
      hlay ⟨((0 : Fin 2), gBase m inner (LGZ.garden.sig 0) z.1.1 ++ z.1.2), (D.gd.ι₁ (P.hp.ιg z)).2⟩]
    simp [addrExt]
  unfold tc2aQG
  rw [hsZ] at hl ⊢
  exact tc2a_side_coh hcan hsa hwg P.decG (bPath m inner) m.green.1 m.green.2 (gBase m inner 1)
    (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs]⟩) (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs]⟩)
    (by simp [bPath]) (by rw [show bPath m inner ++ [m.green.2] = [m.c] ++ inner.lonePath ++ [m.green.2] by
      simp [bPath], nodeSign_chain_child, hsa, slotSign_green])
    (by simpa [bPath] using hg) hla hlb hl h0

end Data

end WaveTurbulence.Flower.ProtRT
