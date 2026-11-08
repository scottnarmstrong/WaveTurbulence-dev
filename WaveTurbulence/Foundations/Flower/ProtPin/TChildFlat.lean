/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT1
public import WaveTurbulence.Foundations.Flower.ProtPin.Flat

/-! # D3 PROT-PIN (P7): flatness of the sub-couples of a traced type-1 side couple

`TcCplAmb p Q LGc`: the couple `LGc` (code `Q`) sits in a canonical garden `H` of level `p + 1` with the layers of `H`.
`tc_t1_flat`: if both roots of a type-1 couple are in layer `p`, its coherent sub-couples are flat in layer `p`
(main's `cpl_coherent` through ProtPin's `flat_couple_piece`, with main's `Embeds.type1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A couple in a canonical ambient, with the ambient layers. -/
def TcCplAmb (p : ℕ) (Q : RegCpl) (LGc : LayeredGarden 2) : Prop :=
  ∃ (w' : ℕ) (H : LayeredGarden w') (a b : Fin w' × TTree.Path), IsCanonGC (p + 1) H ∧ Embeds H.garden Q a b ∧
    ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}

/-- **Coherent sub-couples of a type-1 couple with both roots in layer `p` are flat.** -/
theorem tc_t1_flat {p : ℕ} (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
    (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) (hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true)
    (hA : TcCplAmb p (RegCpl.type1 c Q₁ Q₂ Q₃) LGr) (hr0 : layerAt LGr ((0 : Fin 2), []) = p)
    (hr1 : layerAt LGr ((1 : Fin 2), []) = p) :
    (LG₁.incoherency Q₁.links = 0 → ∀ z, LG₁.layer z = p) ∧
      (LG₂.incoherency Q₂.links = 0 → ∀ z, LG₂.layer z = p) ∧
      (LG₃.incoherency Q₃.links = 0 → ∀ z, LG₃.layer z = p) := by
  obtain ⟨w', H, a, b, hcan, hE, hlay⟩ := hA
  obtain ⟨hw₁, hw₂, hw₃⟩ := tc_t1_wf hwf
  obtain ⟨E₁, E₂, E₃⟩ := hE.type1
  have ha : layerAt H a = p := by
    have h1 := hlay (GNode.root LGr.garden.tree 0)
    rw [← layerAt_node] at h1
    rw [← hr0]
    simpa [addrExt, GNode.root] using h1.symm
  have hb : layerAt H b = p := by
    have h1 := hlay (GNode.root LGr.garden.tree 1)
    rw [← layerAt_node] at h1
    rw [← hr1]
    simpa [addrExt, GNode.root] using h1.symm
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · refine flat_couple_piece hcan hw₁ h.dec₁ E₁ (fun z => ?_) ((parAt_child H p 0 E₁.nodeA).trans ha)
      ((parAt_child H p _ E₁.nodeB).trans hb) h0
    rw [hlA z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιA, t1A, slotA, hz, addrExt]
    · simp [ProtCut.T1Data.ιA, t1A, slotA, hz, addrExt]
  · refine flat_couple_piece hcan hw₂ h.dec₂ E₂ (fun z => ?_) ((parAt_child H p 1 E₂.nodeA).trans hb)
      ((parAt_child H p 1 E₂.nodeB).trans ha) h0
    rw [hlB z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιB, t1B, t1sw, hz, addrExt]
    · simp [ProtCut.T1Data.ιB, t1B, t1sw, hz, addrExt]
  · refine flat_couple_piece hcan hw₃ h.dec₃ E₃ (fun z => ?_) ((parAt_child H p 2 E₃.nodeA).trans ha)
      ((parAt_child H p _ E₃.nodeB).trans hb) h0
    rw [hlC z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιC, t1C, slotC, hz, addrExt]
    · simp [ProtCut.T1Data.ιC, t1C, slotC, hz, addrExt]

/-- A couple placed in a tree object (at `aL, bL`) inherits the canonical ambient of the object. -/
theorem tc_cplAmb_sub {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hdec : Q.Decodes LGc.garden)
    {aL bL : Fin 1 × TTree.Path} (hEL : Embeds LG.garden Q aL bL) {aH bH : Fin w' × TTree.Path}
    (hEH : Embeds H.garden Q aH bH) (haH : aH = addrExt a aL.2) (hbH : bH = addrExt a bL.2)
    (hlayc : ∀ z : GNode LGc.garden.tree,
      LGc.layer z = layerAt LG (addrExt (if z.1.1 = 0 then aL else bL) z.1.2)) : TcCplAmb p Q LGc := by
  subst haH hbH
  refine ⟨w', H, _, _, hcan, hEH, fun z => ?_⟩
  rw [hlayc z]
  rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
  · have hm : z.1.2 ∈ Q.trees.1.nodes := by
      have h2 := z.2
      rw [hz, hdec.2.1] at h2
      exact h2
    rw [if_pos hz, if_pos hz, layerAt_sub hlay hEL.nodeA hEL.treeA hm]
    simp only [addrExt, List.append_assoc]
  · have hne : z.1.1 ≠ 0 := by rw [hz]; decide
    have hm : z.1.2 ∈ Q.trees.2.nodes := by
      have h2 := z.2
      rw [hz, hdec.2.2.1] at h2
      exact h2
    rw [if_neg hne, if_neg hne, layerAt_sub hlay hEL.nodeB hEL.treeB hm]
    simp only [addrExt, List.append_assoc]

/-- A side couple of a chain pair inherits the canonical ambient (oriented by the slot sign `s`). -/
theorem tc_side_amb {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hdec : Q.Decodes LGc.garden)
    (xp bp : TTree.Path) (i1 i2 : Fin 3) (s : ℤˣ) (base : Fin 2 → TTree.Path)
    (hpos : s = 1 → base 0 = [i1] ∧ base 1 = bp ++ [i2]) (hneg : s ≠ 1 → base 0 = bp ++ [i2] ∧ base 1 = [i1])
    (hEL : if s = 1 then Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) [i1])
        (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
      else Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
        (addrExt (addrExt ((0 : Fin 1), []) xp) [i1]))
    (hEH : if s = 1 then Embeds H.garden Q (addrExt (addrExt a xp) [i1]) (addrExt (addrExt a xp) (bp ++ [i2]))
      else Embeds H.garden Q (addrExt (addrExt a xp) (bp ++ [i2])) (addrExt (addrExt a xp) [i1]))
    (hlayc : ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt LG ((0 : Fin 1), xp ++ (base z.1.1 ++ z.1.2))) :
    TcCplAmb p Q LGc := by
  by_cases hs : s = 1
  · rw [if_pos hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hpos hs
    refine tc_cplAmb_sub hcan hlay hdec hEL hEH (by simp [addrExt]) (by simp [addrExt]) (fun z => ?_)
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]
  · rw [if_neg hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hneg hs
    refine tc_cplAmb_sub hcan hlay hdec hEL hEH (by simp [addrExt]) (by simp [addrExt]) (fun z => ?_)
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]

variable {LG LGp LGi : LayeredGarden 1} {LGr' LGg' : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- **The side couples of the terminal cut inherit the canonical ambient.** -/
theorem tc_cut_side_amb (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr' LGg') {p : ℕ}
    (hA : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    TcCplAmb p Qr LGr' ∧ TcCplAmb p Qg LGg' := by
  obtain ⟨w', H, a, h, hcan, hC, hlay⟩ := hA
  have hCL := ChainEmb.of_decodesTree D.dec
  have hCLz := PL234.chainEmb_append_right hCL
  obtain ⟨hrL, hgL, -, -⟩ := hCLz.parts
  have hCz := PL234.chainEmb_append_right hC
  obtain ⟨hr, hg, -, -⟩ := hCz.parts
  refine ⟨?_, ?_⟩
  · exact tc_side_amb hcan hlay D.decR Xp.lonePath ([m.c] ++ inner.lonePath) m.red.1 m.red.2
      (slotSign (LG.garden.sig 0) m.red.1) (rBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [rBase, hs, bPath], by simp [rBase, hs]⟩) hrL hr D.layR
  · exact tc_side_amb hcan hlay D.decG Xp.lonePath ([m.c] ++ inner.lonePath) m.green.1 m.green.2
      (slotSign (LG.garden.sig 0) m.green.1) (gBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [gBase, hs, bPath], by simp [gBase, hs]⟩) hgL hg D.layG

end WaveTurbulence.Flower.ProtPin
