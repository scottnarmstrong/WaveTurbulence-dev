/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2AInc

/-! # D3-HELPER (P7), shape (a+): the pieces in the signed ambient

For the traced couple `Q = type2 (pair m Qr Qg inner rest) Xm Qlp` in its signed canonical ambient (`TcCplAmbS p Q LG`,
roots `a` (`+`), `b` (`-`), both with parent layer `p`), a COHERENT piece is a coherent object of the ambient with its
parent layers (FILT-COH's hypothesis):

* the rest couple `closeCouple rest Xm Qlp`: tree `0` under `𝔫_b` (layer `𝔏_b`), tree `1` under `b` (layer `p`)
  (`tc2a_cohB`; its ambient embedding `tc2a_embeds_close`);
* the interior `inner`: root under `𝔫_1` (layer `p`), lone leaf at `𝔫_b` (`tc2a_cohI`);
* the side couples `Qr`, `Qg`: each tree under `𝔫_1` or `𝔫_b` (`tc2a_cohR`, `tc2a_cohG`, from `tc2a_side_coh`).

Also the layer of a child is at most that of its parent (`tc2a_child_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- An embedded rest couple: chains and lone-pair couple reassembled. -/
theorem tc2a_embeds_close {w : ℕ} {G : Garden w} {rest Xm : RegChain} {Qlp : RegCpl} {a b : Fin w × TTree.Path}
    (hX : ChainEmb G rest 1 a Qlp.trees.1) (hY : ChainEmb G Xm (-1) b Qlp.trees.2)
    (hQ : Embeds G Qlp (addrExt a rest.lonePath) (addrExt b Xm.lonePath)) (hind : Indep a b) :
    Embeds G (SourceApp.closeCouple rest Xm Qlp) a b := by
  unfold SourceApp.closeCouple
  by_cases hn : (rest.isNil && Xm.isNil) = true
  · rw [if_pos hn]
    have hr : rest = .nil := by cases rest <;> simp_all [RegChain.isNil]
    have hm : Xm = .nil := by cases Xm <;> simp_all [RegChain.isNil]
    subst hr hm
    simpa [RegChain.lonePath, addrExt] using hQ
  · rw [if_neg hn]
    refine ⟨hind, hX.node, hY.node, hX.tree, hY.tree, fun q hq ℓ hℓ => ?_⟩
    simp only [RegCpl.pairsAt, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact hX.pairs q hq ℓ hℓ
    · exact hY.pairs q hq ℓ hℓ
    · exact hQ.pairs q hq ℓ hℓ

/-- The layer of a child is at most that of its parent. -/
theorem tc2a_child_le {w : ℕ} (LG : LayeredGarden w) {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (x : Fin w × TTree.Path)
    (i : Fin 3) (hm : (addrExt x [i]).2 ∈ (LG.garden.tree (addrExt x [i]).1).nodes) :
    layerAt LG (addrExt x [i]) ≤ layerAt LG x :=
  (layerAt_le_parAt LG p hle hm).trans (parAt_child LG p i hm).le

/-- **A coherent side couple of a chain pair**, its trees under the pair's two nodes `a` and `a ++ bp`. -/
theorem tc2a_side_coh {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H)
    {a : Fin w' × TTree.Path} (hsa : nodeSign H.garden.sig a = 1) {Q : RegCpl} {LGq : LayeredGarden 2}
    (hwf : Q.wf = true) (hdec : Q.Decodes LGq.garden) (bp : TTree.Path) (i1 i2 : Fin 3) (base : Fin 2 → TTree.Path)
    (hpos : slotSign 1 i1 = 1 → base 0 = [i1] ∧ base 1 = bp ++ [i2])
    (hneg : slotSign 1 i1 ≠ 1 → base 0 = bp ++ [i2] ∧ base 1 = [i1])
    (hbi : bp ++ [i2] ≠ [i1])
    (hs2 : nodeSign H.garden.sig (addrExt a (bp ++ [i2])) = -slotSign 1 i1)
    (hE : if slotSign 1 i1 = 1 then Embeds H.garden Q (addrExt a [i1]) (addrExt a (bp ++ [i2]))
      else Embeds H.garden Q (addrExt a (bp ++ [i2])) (addrExt a [i1]))
    {lA lB : ℕ} (hlA : layerAt H a = lA) (hlB : layerAt H (addrExt a bp) = lB)
    (hlq : ∀ z : GNode LGq.garden.tree, LGq.layer z = layerAt H (addrExt a (base z.1.1 ++ z.1.2)))
    (h0 : LGq.incoherency Q.links = 0) :
    IsCoherentCoupleAt p (if base 0 = [i1] then lA else lB) (if base 1 = [i1] then lA else lB) Q LGq := by
  have hsn : slotSign 1 i1 ≠ 1 → slotSign 1 i1 = -1 := fun hs => by
    rcases Int.units_eq_one_or (slotSign 1 i1) with h | h
    · exact absurd h hs
    · exact h
  have hl : ∀ z : GNode LGq.garden.tree, LGq.layer z =
      layerAt H (addrExt (if z.1.1 = 0 then addrExt a (base 0) else addrExt a (base 1)) z.1.2) := by
    intro z
    rw [hlq z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, addrExt_append]
    · rw [if_neg (by rw [hz]; decide), hz, addrExt_append]
  have hpar1 : ∀ hm : (addrExt a [i1]).2 ∈ (H.garden.tree (addrExt a [i1]).1).nodes,
      parAt H p (addrExt a [i1]) = lA := fun hm => (parAt_child H p i1 hm).trans hlA
  have hpar2 : ∀ hm : (addrExt (addrExt a bp) [i2]).2 ∈ (H.garden.tree (addrExt (addrExt a bp) [i2]).1).nodes,
      parAt H p (addrExt a (bp ++ [i2])) = lB := fun hm => by
    rw [← addrExt_append]; exact (parAt_child H p i2 hm).trans hlB
  have e2 : addrExt (addrExt a bp) [i2] = addrExt a (bp ++ [i2]) := addrExt_append a bp [i2]
  by_cases hs : slotSign 1 i1 = 1
  · rw [if_pos hs] at hE
    obtain ⟨hb0, hb1⟩ := hpos hs
    rw [hb0, hb1, if_pos rfl, if_neg hbi]
    refine ⟨hwf, hdec, w', H, _, _, hcan, hE, ?_, ?_, cohOn_of_couple hdec (by rw [hb0, hb1] at hl; exact hl) h0,
      hpar1 hE.nodeA, hpar2 (by rw [e2]; exact hE.nodeB), by rw [hb0, hb1] at hl; exact hl⟩
    · rw [nodeSign_step, hsa, hs]
    · rw [hs2, hs]
  · rw [if_neg hs] at hE
    obtain ⟨hb0, hb1⟩ := hneg hs
    rw [hb0, hb1, if_pos rfl, if_neg hbi]
    refine ⟨hwf, hdec, w', H, _, _, hcan, hE, ?_, ?_, cohOn_of_couple hdec (by rw [hb0, hb1] at hl; exact hl) h0,
      hpar2 (by rw [e2]; exact hE.nodeA), hpar1 hE.nodeB, by rw [hb0, hb1] at hl; exact hl⟩
    · rw [hs2, hsn hs, neg_neg]
    · rw [nodeSign_step, hsa, hsn hs]

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

theorem tc2a_bnode : bPath m inner ∈ (LG.garden.tree 0).nodes :=
  TTree.branching_subset_nodes _ (D.bR P).2

theorem tc2a_lone_path : (cpair m Qr Qg inner).lonePath = [m.c] ++ inner.lonePath ++ [m.lone] := by
  rw [cpair_lonePath]; simp [lonePos, bPath]

/-- The ambient layers of the root and of `𝔫_b`. -/
theorem tc2a_amb_layers {w' : ℕ} {H : LayeredGarden w'} {a b : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)) :
    layerAt H a = layerAt LG ((0 : Fin 2), []) ∧
      layerAt H (addrExt a (bPath m inner)) = layerAt LG ((0 : Fin 2), bPath m inner) := by
  constructor
  · have h1 := hlay (GNode.root LG.garden.tree 0)
    rw [← layerAt_node] at h1
    simpa [addrExt, GNode.root] using h1.symm
  · have h1 := hlay ⟨((0 : Fin 2), bPath m inner), tc2a_bnode D P⟩
    have h2 := layerAt_of_mem LG (z := ((0 : Fin 2), bPath m inner)) (tc2a_bnode D P)
    rw [h2, h1]
    simp

/-- **The rest couple, when coherent**, is a coherent couple of the ambient, parents `𝔫_b` and `b`. -/
theorem tc2a_cohB {p : ℕ} {rest Xm : RegChain} {Qlp : RegCpl}
    (hA : TcCplAmbS p (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
    (hwB : (SourceApp.closeCouple rest Xm Qlp).wf = true)
    (hdB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden)
    (h0 : LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links = 0) :
    IsCoherentCoupleAt p (layerAt LG ((0 : Fin 2), bPath m inner)) p (SourceApp.closeCouple rest Xm Qlp) LGB := by
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

/-- **The interior, when coherent**, is a coherent tree of the ambient: parent `𝔫_1` (layer `p`), lone leaf `𝔫_b`. -/
theorem tc2a_cohI {p : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : TcCplAmbS p (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
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

/-- The parent layer of a side-couple tree: `lA` under `𝔫_1`, `lB` under `𝔫_b`. -/
def tc2aQR (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (lA lB : ℕ) (t : Fin 2) : ℕ :=
  if rBase m inner ζ t = [m.red.1] then lA else lB

/-- The same for the green couple. -/
def tc2aQG (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (lA lB : ℕ) (t : Fin 2) : ℕ :=
  if gBase m inner ζ t = [m.green.1] then lA else lB

/-- **The red side couple, when coherent.** -/
theorem tc2a_cohR {p : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : TcCplAmbS p (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
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
theorem tc2a_cohG {p : ℕ} {rest Xm : RegChain} {Qlp : RegCpl} (hsZ : LGZ.garden.sig 0 = 1)
    (hA : TcCplAmbS p (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LG)
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

end WaveTurbulence.Flower.ProtPin
