/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ACoh
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack

/-! # RT-GATE: eligibility of the pieces of the root cut of a paired tree

Clause (i) of `MkSlotsO.RootTraceBoundAt`: a regular paired tree `X = pair m Qr Qg inner rest` in its canonical ambient
(`ProtAmbient p X LG`: canonical `H`, chain embedding at `a` with the root sign `ζ = LG.garden.sig 0`, any sign), layers
`≤ p`, chain in ANY layers. D2c's root cut (`RootData`, or `PairOnly` for one pair) has four pieces; here are the facts
that `ProtPin.tc_tree_mixed` / `tc_couple_mixed` ask of them (`ℓ₀` = layer of the root, `ℓb` = layer of `𝔫_b`):

* the suffix `rest`: layers `≤ p`, root layer `≤ ℓb`, lone leaf in the layer `q'` of `X`'s lone leaf, and, when
  coherent, `IsCoherentTreeAt p ℓb q' rest LGs` (`rtc_root_rest`);
* the interior `inner`: layers `≤ p`, root layer `≤ ℓ₀`, lone leaf in layer `ℓb`, coherent ⇒
  `IsCoherentTreeAt p ℓ₀ ℓb` (`rtc_root_inner`, `rtc_pair_inner`);
* the side couples: layers `≤ p`, root layers `≤` their windows `tc2aQR`/`tc2aQG` (`ℓ₀` under `𝔫_a`, `ℓb` under
  `𝔫_b`), coherent ⇒ `IsCoherentCoupleAt p` at those windows (`rtc_root_red/green`, `rtc_pair_red/green`).

`rtc_side_coh` is the signed version of `ProtPin.tc2a_side_coh`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **A coherent side couple of a chain pair**, its trees under the pair's two nodes `a` and `a ++ bp`, the chain at
`a` of sign `ζ`. -/
theorem rtc_side_coh {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H)
    {a : Fin w' × TTree.Path} {ζ : ℤˣ} (hsa : nodeSign H.garden.sig a = ζ) {Q : RegCpl} {LGq : LayeredGarden 2}
    (hwf : Q.wf = true) (hdec : Q.Decodes LGq.garden) (bp : TTree.Path) (i1 i2 : Fin 3) (base : Fin 2 → TTree.Path)
    (hpos : slotSign ζ i1 = 1 → base 0 = [i1] ∧ base 1 = bp ++ [i2])
    (hneg : slotSign ζ i1 ≠ 1 → base 0 = bp ++ [i2] ∧ base 1 = [i1])
    (hbi : bp ++ [i2] ≠ [i1])
    (hs2 : nodeSign H.garden.sig (addrExt a (bp ++ [i2])) = -slotSign ζ i1)
    (hE : if slotSign ζ i1 = 1 then Embeds H.garden Q (addrExt a [i1]) (addrExt a (bp ++ [i2]))
      else Embeds H.garden Q (addrExt a (bp ++ [i2])) (addrExt a [i1]))
    {lA lB : ℕ} (hlA : layerAt H a = lA) (hlB : layerAt H (addrExt a bp) = lB)
    (hlq : ∀ z : GNode LGq.garden.tree, LGq.layer z = layerAt H (addrExt a (base z.1.1 ++ z.1.2)))
    (h0 : LGq.incoherency Q.links = 0) :
    IsCoherentCoupleAt p (if base 0 = [i1] then lA else lB) (if base 1 = [i1] then lA else lB) Q LGq := by
  have hsn : slotSign ζ i1 ≠ 1 → slotSign ζ i1 = -1 := fun hs => by
    rcases Int.units_eq_one_or (slotSign ζ i1) with h | h
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
  by_cases hs : slotSign ζ i1 = 1
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

/-! ### Generic facts for a chain pair at `a` -/

section Generic

variable {LG : LayeredGarden 1} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
  {w' : ℕ} {H : LayeredGarden w'} {a : Fin w' × TTree.Path}

/-- Layers of the object read in the ambient. -/
theorem rtc_layH (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    (x : Fin 1 × TTree.Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes) :
    layerAt LG x = layerAt H (addrExt a x.2) := by
  rw [layerAt_of_mem LG hx]
  exact hlay ⟨x, hx⟩

theorem rtc_layH0 (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)) :
    layerAt LG ((0 : Fin 1), []) = layerAt H a := by
  rw [rtc_layH hlay _ (TTree.nil_mem_nodes _)]
  simp [addrExt]

/-- **The interior, when coherent**: parent `𝔫_a` (layer `ℓ₀`), lone leaf `𝔫_b` (layer `ℓb`). -/
theorem rtc_inner_coh {p : ℕ} (hcan : IsCanonGC (p + 1) H) {h : TTree}
    (hC : ChainEmb H.garden (RegChain.pair m Qr Qg inner rest) (LG.garden.sig 0) a h)
    (hsa : nodeSign H.garden.sig a = LG.garden.sig 0)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {LGi : LayeredGarden 1} (hwI : inner.wf = true) (hdI : inner.DecodesTree LGi.garden)
    (hsI : LGi.garden.sig 0 = slotSign (LG.garden.sig 0) m.c)
    (hlI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), m.c :: z.1.2))
    (hmI : ∀ z : GNode LGi.garden.tree, m.c :: z.1.2 ∈ (LG.garden.tree 0).nodes)
    (hmb : bPath m inner ∈ (LG.garden.tree 0).nodes)
    (h0 : LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0) :
    IsCoherentTreeAt p (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) inner LGi := by
  obtain ⟨-, -, hI, -⟩ := hC.parts
  have hl : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt H (addrExt (addrExt a [m.c]) z.1.2) := by
    intro z
    rw [hlI z, rtc_layH hlay ((0 : Fin 1), m.c :: z.1.2) (hmI z)]
    simp [addrExt]
  refine ⟨hwI, hdI, w', H, addrExt a [m.c], _, hcan, by rw [hsI]; exact hI, ?_, cohOn_of_tree hdI hl h0, ?_, ?_,
    hl⟩
  · rw [nodeSign_step, hsa, hsI]
  · rw [parAt_child H p m.c hI.node, rtc_layH0 hlay]
  · rw [rtc_layH hlay ((0 : Fin 1), bPath m inner) hmb, addrExt_append]
    rfl

theorem rtc_inner_lone {LGi : LayeredGarden 1}
    (hlI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), m.c :: z.1.2)) :
    ∀ z : GNode LGi.garden.tree, z.1.2 = inner.lonePath → LGi.layer z = layerAt LG ((0 : Fin 1), bPath m inner) := by
  intro z hz
  rw [hlI z, hz]
  rfl

theorem rtc_inner_root {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) {LGi : LayeredGarden 1}
    (hlI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), m.c :: z.1.2))
    (hmI : ∀ z : GNode LGi.garden.tree, m.c :: z.1.2 ∈ (LG.garden.tree 0).nodes) :
    LGi.layer (GNode.root LGi.garden.tree 0) ≤ layerAt LG ((0 : Fin 1), []) := by
  have hm : [m.c] ∈ (LG.garden.tree 0).nodes := by
    simpa [GNode.root] using hmI (GNode.root LGi.garden.tree 0)
  have := tc2a_child_le LG hle ((0 : Fin 1), []) m.c hm
  rw [hlI]
  simpa [addrExt, GNode.root] using this

/-- **The suffix, when coherent**: parent `𝔫_b` (layer `ℓb`), lone leaf in the layer `q'` of `X`'s lone leaf. -/
theorem rtc_rest_coh {p : ℕ} (hcan : IsCanonGC (p + 1) H) {h : TTree}
    (hC : ChainEmb H.garden (RegChain.pair m Qr Qg inner rest) (LG.garden.sig 0) a h)
    (hsa : nodeSign H.garden.sig a = LG.garden.sig 0)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {LGs : LayeredGarden 1} (hwS : rest.wf = true) (hdS : rest.DecodesTree LGs.garden)
    (hsS : LGs.garden.sig 0 = LG.garden.sig 0)
    (hlS : ∀ z : GNode LGs.garden.tree, LGs.layer z = layerAt LG ((0 : Fin 1), lonePos m inner ++ z.1.2))
    (hmS : ∀ z : GNode LGs.garden.tree, lonePos m inner ++ z.1.2 ∈ (LG.garden.tree 0).nodes)
    (hmb : bPath m inner ∈ (LG.garden.tree 0).nodes) {q' : ℕ}
    (hml : (RegChain.pair m Qr Qg inner rest).lonePath ∈ (LG.garden.tree 0).nodes)
    (hq' : ∀ z : GNode LG.garden.tree, z.1.2 = (RegChain.pair m Qr Qg inner rest).lonePath → LG.layer z = q')
    (h0 : LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) = 0) :
    IsCoherentTreeAt p (layerAt LG ((0 : Fin 1), bPath m inner)) q' rest LGs := by
  have hCs := PL234.chainEmb_append_right (B := cpair m Qr Qg inner) (D := rest) hC
  rw [cpair_lonePath] at hCs
  have hlp : (RegChain.pair m Qr Qg inner rest).lonePath = lonePos m inner ++ rest.lonePath := by
    simp [RegChain.lonePath, lonePos, bPath]
  have hl : ∀ z : GNode LGs.garden.tree, LGs.layer z =
      layerAt H (addrExt (addrExt a (lonePos m inner)) z.1.2) := by
    intro z
    rw [hlS z, rtc_layH hlay ((0 : Fin 1), lonePos m inner ++ z.1.2) (hmS z), addrExt_append]
  have e : addrExt a (lonePos m inner) = addrExt (addrExt a (bPath m inner)) [m.lone] := by
    rw [addrExt_append]; rfl
  refine ⟨hwS, hdS, w', H, addrExt a (lonePos m inner), h, hcan, by rw [hsS]; exact hCs, ?_,
    cohOn_of_tree hdS hl h0, ?_, ?_, hl⟩
  · rw [hsS, ← cpair_lonePath m Qr Qg inner, nodeSign_spine, hsa]
  · rw [e, parAt_child H p m.lone (by rw [← e]; exact hCs.node), rtc_layH hlay ((0 : Fin 1), bPath m inner) hmb]
  · rw [addrExt_append, ← hlp]
    exact (rtc_layH hlay ((0 : Fin 1), _) hml).symm.trans ((layerAt_of_mem LG hml).trans (hq' _ rfl))

theorem rtc_rest_root {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) {LGs : LayeredGarden 1}
    (hlS : ∀ z : GNode LGs.garden.tree, LGs.layer z = layerAt LG ((0 : Fin 1), lonePos m inner ++ z.1.2))
    (hmS : ∀ z : GNode LGs.garden.tree, lonePos m inner ++ z.1.2 ∈ (LG.garden.tree 0).nodes) :
    LGs.layer (GNode.root LGs.garden.tree 0) ≤ layerAt LG ((0 : Fin 1), bPath m inner) := by
  have hm : bPath m inner ++ [m.lone] ∈ (LG.garden.tree 0).nodes := by
    simpa [lonePos, GNode.root] using hmS (GNode.root LGs.garden.tree 0)
  have := tc2a_child_le LG hle ((0 : Fin 1), bPath m inner) m.lone hm
  rw [hlS]
  simpa [addrExt, lonePos, GNode.root] using this

theorem rtc_rest_lone {LGs : LayeredGarden 1}
    (hlS : ∀ z : GNode LGs.garden.tree, LGs.layer z = layerAt LG ((0 : Fin 1), lonePos m inner ++ z.1.2))
    (hmS : ∀ z : GNode LGs.garden.tree, lonePos m inner ++ z.1.2 ∈ (LG.garden.tree 0).nodes) {q' : ℕ}
    (hq' : ∀ z : GNode LG.garden.tree, z.1.2 = (RegChain.pair m Qr Qg inner rest).lonePath → LG.layer z = q') :
    ∀ z : GNode LGs.garden.tree, z.1.2 = rest.lonePath → LGs.layer z = q' := by
  intro z hz
  rw [hlS z, layerAt_of_mem LG (z := ((0 : Fin 1), lonePos m inner ++ z.1.2)) (hmS z)]
  refine hq' _ ?_
  show lonePos m inner ++ z.1.2 = _
  rw [hz]
  simp [RegChain.lonePath, lonePos, bPath]

/-- **The red side couple, when coherent.** -/
theorem rtc_red_coh {p : ℕ} (hcan : IsCanonGC (p + 1) H) {h : TTree}
    (hC : ChainEmb H.garden (RegChain.pair m Qr Qg inner rest) (LG.garden.sig 0) a h)
    (hsa : nodeSign H.garden.sig a = LG.garden.sig 0)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {LGr : LayeredGarden 2} (hwr : Qr.wf = true) (hdr : Qr.Decodes LGr.garden)
    (hlR : ∀ z : GNode LGr.garden.tree,
      LGr.layer z = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))
    (hmR : ∀ z : GNode LGr.garden.tree, rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes)
    (hmb : bPath m inner ∈ (LG.garden.tree 0).nodes) (h0 : LGr.incoherency Qr.links = 0) :
    IsCoherentCoupleAt p
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qr LGr := by
  obtain ⟨hr, -, -, -⟩ := hC.parts
  have hl : ∀ z : GNode LGr.garden.tree, LGr.layer z =
      layerAt H (addrExt a (rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)) := fun z => by
    rw [hlR z, rtc_layH hlay ((0 : Fin 1), _) (hmR z)]
  unfold tc2aQR
  exact rtc_side_coh hcan hsa hwr hdr (bPath m inner) m.red.1 m.red.2 (rBase m inner (LG.garden.sig 0))
    (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs]⟩) (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs]⟩)
    (by simp [bPath]) (by rw [show bPath m inner ++ [m.red.2] = [m.c] ++ inner.lonePath ++ [m.red.2] by
      simp [bPath], nodeSign_chain_child, hsa, slotSign_red])
    (by simpa [bPath] using hr) (rtc_layH0 hlay).symm (rtc_layH hlay ((0 : Fin 1), bPath m inner) hmb).symm hl h0

/-- **The green side couple, when coherent.** -/
theorem rtc_green_coh {p : ℕ} (hcan : IsCanonGC (p + 1) H) {h : TTree}
    (hC : ChainEmb H.garden (RegChain.pair m Qr Qg inner rest) (LG.garden.sig 0) a h)
    (hsa : nodeSign H.garden.sig a = LG.garden.sig 0)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {LGg : LayeredGarden 2} (hwg : Qg.wf = true) (hdg : Qg.Decodes LGg.garden)
    (hlG : ∀ z : GNode LGg.garden.tree,
      LGg.layer z = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))
    (hmG : ∀ z : GNode LGg.garden.tree, gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes)
    (hmb : bPath m inner ∈ (LG.garden.tree 0).nodes) (h0 : LGg.incoherency Qg.links = 0) :
    IsCoherentCoupleAt p
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 0)
      (tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) 1)
      Qg LGg := by
  obtain ⟨-, hg, -, -⟩ := hC.parts
  have hl : ∀ z : GNode LGg.garden.tree, LGg.layer z =
      layerAt H (addrExt a (gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)) := fun z => by
    rw [hlG z, rtc_layH hlay ((0 : Fin 1), _) (hmG z)]
  unfold tc2aQG
  exact rtc_side_coh hcan hsa hwg hdg (bPath m inner) m.green.1 m.green.2 (gBase m inner (LG.garden.sig 0))
    (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs]⟩) (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs]⟩)
    (by simp [bPath]) (by rw [show bPath m inner ++ [m.green.2] = [m.c] ++ inner.lonePath ++ [m.green.2] by
      simp [bPath], nodeSign_chain_child, hsa, slotSign_green])
    (by simpa [bPath] using hg) (rtc_layH0 hlay).symm (rtc_layH hlay ((0 : Fin 1), bPath m inner) hmb).symm hl h0

/-- Root layers of the red couple are at most their windows. -/
theorem rtc_red_root {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) {LGr : LayeredGarden 2}
    (hlR : ∀ z : GNode LGr.garden.tree,
      LGr.layer z = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))
    (hmR : ∀ z : GNode LGr.garden.tree, rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes)
    (t : Fin 2) :
    LGr.layer (GNode.root LGr.garden.tree t) ≤
      tc2aQR m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t := by
  have hm : rBase m inner (LG.garden.sig 0) t ∈ (LG.garden.tree 0).nodes := by
    simpa [GNode.root] using hmR (GNode.root LGr.garden.tree t)
  have hl : LGr.layer (GNode.root LGr.garden.tree t) = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) t) := by
    rw [hlR]; simp [GNode.root]
  rw [hl]
  unfold tc2aQR
  split_ifs with hb
  · rw [hb] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 1), []) m.red.1 hm
  · have hb' : rBase m inner (LG.garden.sig 0) t = bPath m inner ++ [m.red.2] := by
      unfold rBase at hb ⊢
      split_ifs at hb ⊢ with hh
      · exact absurd rfl hb
      · rfl
    rw [hb'] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 1), bPath m inner) m.red.2 hm

/-- Root layers of the green couple are at most their windows. -/
theorem rtc_green_root {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) {LGg : LayeredGarden 2}
    (hlG : ∀ z : GNode LGg.garden.tree,
      LGg.layer z = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2))
    (hmG : ∀ z : GNode LGg.garden.tree, gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2 ∈ (LG.garden.tree 0).nodes)
    (t : Fin 2) :
    LGg.layer (GNode.root LGg.garden.tree t) ≤
      tc2aQG m inner (LG.garden.sig 0) (layerAt LG ((0 : Fin 1), [])) (layerAt LG ((0 : Fin 1), bPath m inner)) t := by
  have hm : gBase m inner (LG.garden.sig 0) t ∈ (LG.garden.tree 0).nodes := by
    simpa [GNode.root] using hmG (GNode.root LGg.garden.tree t)
  have hl : LGg.layer (GNode.root LGg.garden.tree t) = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) t) := by
    rw [hlG]; simp [GNode.root]
  rw [hl]
  unfold tc2aQG
  split_ifs with hb
  · rw [hb] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 1), []) m.green.1 hm
  · have hb' : gBase m inner (LG.garden.sig 0) t = bPath m inner ++ [m.green.2] := by
      unfold gBase at hb ⊢
      split_ifs at hb ⊢ with hh
      · exact absurd rfl hb
      · rfl
    rw [hb'] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 1), bPath m inner) m.green.2 hm

end Generic

end WaveTurbulence.Flower.ProtRT
