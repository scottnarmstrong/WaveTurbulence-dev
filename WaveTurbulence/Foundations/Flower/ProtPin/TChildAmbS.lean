/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFlat
public import WaveTurbulence.Foundations.Flower.ProtPin.Ambient

/-! # D3 PROT-PIN (P7): the signed canonical ambient of the traced side couple

`TcCplAmbS p Q LGc`: `TcCplAmb` with the ambient signs `+1` at the root of tree `0` and `-1` at the root of tree `1`
(the sign clause of main's `IsCoherentCoupleAt`). `tc_cut_side_ambS`: the side couples of the terminal cut of a
protected paired tree carry it (from `ProtAmbient`, whose sign is transported along the chain by main's
`nodeSign_spine`, `nodeSign_chain_child`, `slotSign_red/green`). `tc_protAmb_of_cap`: the paired tree of a cap couple
inherits the signed ambient. `tc_t1_coh`: a coherent sub-couple of a type-1 couple in `TcCplAmbS` is
`IsCoherentCoupleAt` with the root layers of the couple as parent layers (any two layers). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A couple in a canonical ambient with the ambient layers, the couple's signs and both parents in layer `p`. -/
def TcCplAmbS (p : ℕ) (Q : RegCpl) (LGc : LayeredGarden 2) : Prop :=
  ∃ (w' : ℕ) (H : LayeredGarden w') (a b : Fin w' × TTree.Path), IsCanonGC (p + 1) H ∧ Embeds H.garden Q a b ∧
    nodeSign H.garden.sig a = 1 ∧ nodeSign H.garden.sig b = -1 ∧ parAt H p a = p ∧ parAt H p b = p ∧
    ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)

theorem TcCplAmbS.amb {p : ℕ} {Q : RegCpl} {LGc : LayeredGarden 2} (h : TcCplAmbS p Q LGc) : TcCplAmb p Q LGc := by
  obtain ⟨w', H, a, b, hc, hE, -, -, -, -, hl⟩ := h
  exact ⟨w', H, a, b, hc, hE, hl⟩

/-- A couple placed in a tree object inherits the signed canonical ambient. -/
theorem tc_cplAmb_subS {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hdec : Q.Decodes LGc.garden)
    {aL bL : Fin 1 × TTree.Path} (hEL : Embeds LG.garden Q aL bL) {aH bH : Fin w' × TTree.Path}
    (hEH : Embeds H.garden Q aH bH) (haH : aH = addrExt a aL.2) (hbH : bH = addrExt a bL.2)
    (hsa : nodeSign H.garden.sig aH = 1) (hsb : nodeSign H.garden.sig bH = -1)
    (hpa : parAt H p aH = p) (hpb : parAt H p bH = p)
    (hlayc : ∀ z : GNode LGc.garden.tree,
      LGc.layer z = layerAt LG (addrExt (if z.1.1 = 0 then aL else bL) z.1.2)) : TcCplAmbS p Q LGc := by
  subst haH hbH
  refine ⟨w', H, _, _, hcan, hEH, hsa, hsb, hpa, hpb, fun z => ?_⟩
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

/-- A side couple of a chain pair inherits the signed ambient (oriented by the slot sign `s`). -/
theorem tc_side_ambS {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hdec : Q.Decodes LGc.garden)
    (xp bp : TTree.Path) (i1 i2 : Fin 3) (s : ℤˣ) (base : Fin 2 → TTree.Path)
    (hpos : s = 1 → base 0 = [i1] ∧ base 1 = bp ++ [i2]) (hneg : s ≠ 1 → base 0 = bp ++ [i2] ∧ base 1 = [i1])
    (hs1 : nodeSign H.garden.sig (addrExt (addrExt a xp) [i1]) = s)
    (hs2 : nodeSign H.garden.sig (addrExt (addrExt a xp) (bp ++ [i2])) = -s)
    (hpa1 : layerAt H (addrExt a xp) = p) (hpa2 : layerAt H (addrExt (addrExt a xp) bp) = p)
    (hEL : if s = 1 then Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) [i1])
        (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
      else Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
        (addrExt (addrExt ((0 : Fin 1), []) xp) [i1]))
    (hEH : if s = 1 then Embeds H.garden Q (addrExt (addrExt a xp) [i1]) (addrExt (addrExt a xp) (bp ++ [i2]))
      else Embeds H.garden Q (addrExt (addrExt a xp) (bp ++ [i2])) (addrExt (addrExt a xp) [i1]))
    (hlayc : ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt LG ((0 : Fin 1), xp ++ (base z.1.1 ++ z.1.2))) :
    TcCplAmbS p Q LGc := by
  have hsn : s ≠ 1 → s = -1 := fun hs => by
    rcases Int.units_eq_one_or s with h | h
    · exact absurd h hs
    · exact h
  have hq1 : ∀ (E : Embeds H.garden Q (addrExt (addrExt a xp) [i1]) (addrExt (addrExt a xp) (bp ++ [i2])) ∨
      Embeds H.garden Q (addrExt (addrExt a xp) (bp ++ [i2])) (addrExt (addrExt a xp) [i1])),
      parAt H p (addrExt (addrExt a xp) [i1]) = p ∧ parAt H p (addrExt (addrExt a xp) (bp ++ [i2])) = p := by
    intro E
    have hm1 : (addrExt (addrExt a xp) [i1]).2 ∈ (H.garden.tree (addrExt (addrExt a xp) [i1]).1).nodes := by
      rcases E with E | E
      · exact E.nodeA
      · exact E.nodeB
    have hm2 : (addrExt (addrExt (addrExt a xp) bp) [i2]).2 ∈
        (H.garden.tree (addrExt (addrExt (addrExt a xp) bp) [i2]).1).nodes := by
      have e : addrExt (addrExt (addrExt a xp) bp) [i2] = addrExt (addrExt a xp) (bp ++ [i2]) := by
        simp [addrExt, List.append_assoc]
      rw [e]
      rcases E with E | E
      · exact E.nodeB
      · exact E.nodeA
    refine ⟨(parAt_child H p i1 hm1).trans hpa1, ?_⟩
    have e : addrExt (addrExt a xp) (bp ++ [i2]) = addrExt (addrExt (addrExt a xp) bp) [i2] := by
      simp [addrExt, List.append_assoc]
    rw [e]
    exact (parAt_child H p i2 hm2).trans hpa2
  by_cases hs : s = 1
  · rw [if_pos hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hpos hs
    obtain ⟨hp1, hp2⟩ := hq1 (Or.inl hEH)
    refine tc_cplAmb_subS hcan hlay hdec hEL hEH (by simp [addrExt]) (by simp [addrExt])
      (by rw [hs1, hs]) (by rw [hs2, hs]) hp1 hp2 (fun z => ?_)
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]
  · rw [if_neg hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hneg hs
    obtain ⟨hp1, hp2⟩ := hq1 (Or.inr hEH)
    refine tc_cplAmb_subS hcan hlay hdec hEL hEH (by simp [addrExt]) (by simp [addrExt])
      (by rw [hs2, hsn hs, neg_neg]) (by rw [hs1, hsn hs]) hp2 hp1 (fun z => ?_)
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]

variable {LG LGp LGi : LayeredGarden 1} {LGr' LGg' : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- **The side couples of the terminal cut inherit the signed ambient.** -/
theorem tc_cut_side_ambS (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr' LGg') {p : ℕ}
    (hA : ProtAmbient p (appendChain Xp (cpair m Qr Qg inner)) LG)
    (hna : ∃ hm : Xp.lonePath ∈ (LG.garden.tree 0).nodes, LG.layer ⟨((0 : Fin 1), Xp.lonePath), hm⟩ = p)
    (hnb : ∃ hm : Xp.lonePath ++ bPath m inner ∈ (LG.garden.tree 0).nodes,
      LG.layer ⟨((0 : Fin 1), Xp.lonePath ++ bPath m inner), hm⟩ = p) :
    TcCplAmbS p Qr LGr' ∧ TcCplAmbS p Qg LGg' := by
  obtain ⟨w', H, a, h, hcan, hC, hsg, hlay⟩ := hA
  obtain ⟨hma, hla⟩ := hna
  obtain ⟨hmb, hlb⟩ := hnb
  have hpa1 : layerAt H (addrExt a Xp.lonePath) = p :=
    (hlay (⟨((0 : Fin 1), Xp.lonePath), hma⟩ : GNode LG.garden.tree)).symm.trans hla
  have hpa2 : layerAt H (addrExt (addrExt a Xp.lonePath) ([m.c] ++ inner.lonePath)) = p := by
    have := (hlay (⟨((0 : Fin 1), Xp.lonePath ++ bPath m inner), hmb⟩ : GNode LG.garden.tree)).symm.trans hlb
    simpa [addrExt, bPath, List.append_assoc] using this
  have hCL := ChainEmb.of_decodesTree D.dec
  have hCLz := PL234.chainEmb_append_right hCL
  obtain ⟨hrL, hgL, -, -⟩ := hCLz.parts
  have hCz := PL234.chainEmb_append_right hC
  obtain ⟨hr, hg, -, -⟩ := hCz.parts
  have hsx : nodeSign H.garden.sig (addrExt a Xp.lonePath) = LG.garden.sig 0 := by
    rw [nodeSign_spine, hsg]
  refine ⟨?_, ?_⟩
  · exact tc_side_ambS hcan hlay D.decR Xp.lonePath ([m.c] ++ inner.lonePath) m.red.1 m.red.2
      (slotSign (LG.garden.sig 0) m.red.1) (rBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [rBase, hs, bPath], by simp [rBase, hs]⟩)
      (by rw [nodeSign_step, hsx]) (by rw [nodeSign_chain_child, hsx, slotSign_red]) hpa1 hpa2 hrL hr D.layR
  · exact tc_side_ambS hcan hlay D.decG Xp.lonePath ([m.c] ++ inner.lonePath) m.green.1 m.green.2
      (slotSign (LG.garden.sig 0) m.green.1) (gBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [gBase, hs, bPath], by simp [gBase, hs]⟩)
      (by rw [nodeSign_step, hsx]) (by rw [nodeSign_chain_child, hsx, slotSign_green]) hpa1 hpa2 hgL hg D.layG

/-- The two chain nodes of the terminal pair are in layer `p`. -/
theorem tc_cut_nab (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr' LGg') {p : ℕ}
    (h : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    (∃ hm : Xp.lonePath ∈ (LG.garden.tree 0).nodes, LG.layer ⟨((0 : Fin 1), Xp.lonePath), hm⟩ = p) ∧
    (∃ hm : Xp.lonePath ++ bPath m inner ∈ (LG.garden.tree 0).nodes,
      LG.layer ⟨((0 : Fin 1), Xp.lonePath ++ bPath m inner), hm⟩ = p) := by
  have hch := h.2.2.2
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  have hlp : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (bPath m inner ++ [m.lone]) := by
    rw [appendChain_lonePath, cpair_lonePath]; rfl
  have hab : Xp.lonePath ∈ (LG.garden.tree 0).branching := by
    have := (D.aB hZ hsZ).2; rw [D.aB_path hZ hsZ] at this; exact this
  have hbb : Xp.lonePath ++ bPath m inner ∈ (LG.garden.tree 0).branching := by
    have := (D.bG hZ hsZ).2; rw [D.bG_path hZ hsZ] at this; exact this
  refine ⟨⟨TTree.branching_subset_nodes _ hab, ?_⟩, ⟨TTree.branching_subset_nodes _ hbb, ?_⟩⟩
  · exact hch ⟨((0 : Fin 1), Xp.lonePath), hab⟩ rfl (by rw [hlp]; exact List.prefix_append _ _)
      (by rw [hlp]; simp [bPath])
  · exact hch ⟨((0 : Fin 1), Xp.lonePath ++ bPath m inner), hbb⟩ rfl
      (by rw [hlp, ← List.append_assoc]; exact List.prefix_append _ _) (by rw [hlp]; simp)

/-- **The paired tree of a cap couple inherits the signed ambient.** -/
theorem tc_protAmb_of_cap {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1}
    (hA : ProtAmbient p X LG) (D : ProtCut.CapData X LG LG1) : ProtAmbient p X LG1 := by
  obtain ⟨w', H, a, b, ζ, X₀, hc, hE, hs, hX, -, -, -, hl⟩ := hA
  have key : ∃ (w'' : ℕ) (H' : LayeredGarden w'') (a' : Fin w'' × TTree.Path), IsCanonGC (p + 1) H' ∧
      ChainEmb H'.garden X 1 a' .leaf ∧ nodeSign H'.garden.sig a' = 1 ∧
      ∀ z : GNode LG.garden.tree, z.1.1 = 0 → LG.layer z = layerAt H' (addrExt a' z.1.2) := by
    rcases Int.units_eq_one_or ζ with rfl | rfl
    · rw [if_pos rfl] at hX
      subst hX
      exact ⟨w', H, a, hc, hE, hs, fun z hz => by rw [hl z, if_pos hz]⟩
    · rw [if_neg units_neg_one_ne_one] at hX
      subst hX
      obtain ⟨e, hce⟩ := exists_conj_canon hc
      have hconj := ConjCoh.conjLayered_isConjugateBy H e
      have hE' := ZpSurj.chainEmb_conj hconj hE
      rw [neg_neg] at hE'
      refine ⟨w', ConjCoh.conjLayered H e, ConjCoh.phi e a, hce, hE', ?_, fun z hz => ?_⟩
      · rw [ConjCoh.nodeSign_conj hconj, hs, neg_neg]
      · rw [hl z, if_pos hz]
        exact (ConjCoh.layerAt_conj hconj (addrExt a z.1.2)).symm
  obtain ⟨w'', H', a', hc', hE', hs', hl'⟩ := key
  refine ⟨w'', H', a', .leaf, hc', by rw [D.sig1]; exact hE', by rw [D.sig1]; exact hs', fun z => ?_⟩
  rw [D.lay z]
  have hz0 : z.1.1 = 0 := Subsingleton.elim _ _
  have hz : z.1.2 ∈ (LG.garden.tree (0 : Fin 2)).nodes := by
    have h2 := z.2
    rw [hz0, D.treeT] at h2
    rw [D.tree0]
    exact h2
  rw [layerAt_of_mem LG (z := ((0 : Fin 2), z.1.2)) hz, hl' ⟨((0 : Fin 2), z.1.2), hz⟩ rfl]

/-! ### Coherent sub-couples of a type-1 couple -/

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGr LG₁ LG₂ LG₃ : LayeredGarden 2}

theorem tc_partner_ne_one (c : MiniCplCode) (x : Fin 3) (hx : x ≠ 1) : c.partner x ≠ 1 := by
  revert hx
  fin_cases c <;> fin_cases x <;> decide

/-- **Coherent sub-couples of a type-1 couple are coherent couples of the ambient**, with the root layers of the
couple as parent layers (`A`, `C`: tree `0` under root `0`; `B`: tree `0` under root `1`). -/
theorem tc_t1_cohR {p : ℕ} (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
    (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) (hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true)
    {w' : ℕ} {H : LayeredGarden w'} {a b : Fin w' × TTree.Path} (hcan : IsCanonGC (p + 1) H)
    (hE : Embeds H.garden (RegCpl.type1 c Q₁ Q₂ Q₃) a b) (hsa : nodeSign H.garden.sig a = 1)
    (hsb : nodeSign H.garden.sig b = -1)
    (hlay : ∀ z : GNode LGr.garden.tree, LGr.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)) :
    (LG₁.incoherency Q₁.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((0 : Fin 2), [])) (layerAt LGr ((1 : Fin 2), [])) Q₁ LG₁) ∧
      (LG₂.incoherency Q₂.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((1 : Fin 2), [])) (layerAt LGr ((0 : Fin 2), [])) Q₂ LG₂) ∧
      (LG₃.incoherency Q₃.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((0 : Fin 2), [])) (layerAt LGr ((1 : Fin 2), [])) Q₃ LG₃) := by
  obtain ⟨hw₁, hw₂, hw₃⟩ := tc_t1_wf hwf
  obtain ⟨E₁, E₂, E₃⟩ := hE.type1
  have ha : layerAt H a = layerAt LGr ((0 : Fin 2), []) := by
    have h1 := hlay (GNode.root LGr.garden.tree 0)
    rw [← layerAt_node] at h1
    simpa [addrExt, GNode.root] using h1.symm
  have hb : layerAt H b = layerAt LGr ((1 : Fin 2), []) := by
    have h1 := hlay (GNode.root LGr.garden.tree 1)
    rw [← layerAt_node] at h1
    simpa [addrExt, GNode.root] using h1.symm
  have hsg : ∀ (x : Fin w' × TTree.Path) (σ : ℤˣ) (i : Fin 3), nodeSign H.garden.sig x = σ →
      nodeSign H.garden.sig (addrExt x [i]) = slotSign σ i := fun x σ i hx => by rw [nodeSign_step, hx]
  have hl₁ : ∀ z : GNode LG₁.garden.tree, LG₁.layer z =
      layerAt H (addrExt (if z.1.1 = 0 then addrExt a [0] else addrExt b [c.partner 0]) z.1.2) := fun z => by
    rw [hlA z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιA, t1A, slotA, hz, addrExt]
    · simp [ProtCut.T1Data.ιA, t1A, slotA, hz, addrExt]
  have hl₂ : ∀ z : GNode LG₂.garden.tree, LG₂.layer z =
      layerAt H (addrExt (if z.1.1 = 0 then addrExt b [1] else addrExt a [1]) z.1.2) := fun z => by
    rw [hlB z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιB, t1B, t1sw, hz, addrExt]
    · simp [ProtCut.T1Data.ιB, t1B, t1sw, hz, addrExt]
  have hl₃ : ∀ z : GNode LG₃.garden.tree, LG₃.layer z =
      layerAt H (addrExt (if z.1.1 = 0 then addrExt a [2] else addrExt b [c.partner 2]) z.1.2) := fun z => by
    rw [hlC z, hlay]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · simp [ProtCut.T1Data.ιC, t1C, slotC, hz, addrExt]
    · simp [ProtCut.T1Data.ιC, t1C, slotC, hz, addrExt]
  have hp0 : c.partner 0 ≠ 1 := tc_partner_ne_one c 0 (by decide)
  have hp2 : c.partner 2 ≠ 1 := tc_partner_ne_one c 2 (by decide)
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · refine ⟨hw₁, h.dec₁, w', H, _, _, hcan, E₁, ?_, ?_, cohOn_of_couple h.dec₁ hl₁ h0,
      (parAt_child H p 0 E₁.nodeA).trans ha, (parAt_child H p _ E₁.nodeB).trans hb, hl₁⟩
    · rw [hsg a 1 0 hsa]; decide
    · rw [hsg b (-1) _ hsb]; simp [slotSign, hp0]
  · refine ⟨hw₂, h.dec₂, w', H, _, _, hcan, E₂, ?_, ?_, cohOn_of_couple h.dec₂ hl₂ h0,
      (parAt_child H p 1 E₂.nodeA).trans hb, (parAt_child H p 1 E₂.nodeB).trans ha, hl₂⟩
    · rw [hsg b (-1) 1 hsb]; simp [slotSign]
    · rw [hsg a 1 1 hsa]; simp [slotSign]
  · refine ⟨hw₃, h.dec₃, w', H, _, _, hcan, E₃, ?_, ?_, cohOn_of_couple h.dec₃ hl₃ h0,
      (parAt_child H p 2 E₃.nodeA).trans ha, (parAt_child H p _ E₃.nodeB).trans hb, hl₃⟩
    · rw [hsg a 1 2 hsa]; decide
    · rw [hsg b (-1) _ hsb]; simp [slotSign, hp2]

theorem tc_t1_coh {p : ℕ} (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
    (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) (hwf : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true)
    (hA : TcCplAmbS p (RegCpl.type1 c Q₁ Q₂ Q₃) LGr) :
    (LG₁.incoherency Q₁.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((0 : Fin 2), [])) (layerAt LGr ((1 : Fin 2), [])) Q₁ LG₁) ∧
      (LG₂.incoherency Q₂.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((1 : Fin 2), [])) (layerAt LGr ((0 : Fin 2), [])) Q₂ LG₂) ∧
      (LG₃.incoherency Q₃.links = 0 →
        IsCoherentCoupleAt p (layerAt LGr ((0 : Fin 2), [])) (layerAt LGr ((1 : Fin 2), [])) Q₃ LG₃) := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, -, -, hlay⟩ := hA
  exact tc_t1_cohR h hlA hlB hlC hwf hcan hE hsa hsb hlay

end WaveTurbulence.Flower.ProtPin
