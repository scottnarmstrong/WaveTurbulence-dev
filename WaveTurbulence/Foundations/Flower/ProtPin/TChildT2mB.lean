/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFix
public import WaveTurbulence.Foundations.Flower.ProtCut.T2mKer
public import WaveTurbulence.Foundations.Flower.ProtCut.T2mExist

/-! # D3 PROT-PIN (P7): bookkeeping of a type-2 traced couple with an empty `-` chain (o104 (c−))

For `Q = type2 Xp nil (type1 c Q₁ Q₂ Q₃)` decoding `LG` (`T2mData LG Xp LGX LGQ`: the chain `Xp` as the paired tree
`LGX`, the lone-pair couple `LGQ`): sizes, the gate-form multiplier and star cost split through the glue
(`tc2_mult`, `tc2_cost`), leaves (`tc2_leafwise`, `tc2_leafSize`), layers, and the incoherency split
`tc2_incoh`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem tc2_sizes {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {n : ℕ}
    (hsz : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).size = 2 * n) :
    ∃ nX n₁ n₂ n₃ : ℕ, Xp.size = 2 * nX ∧ Q₁.size = 2 * n₁ ∧ Q₂.size = 2 * n₂ ∧ Q₃.size = 2 * n₃ ∧
      nX + n₁ + n₂ + n₃ + 1 = n := by
  obtain ⟨nX, hX⟩ := chain_size_even Xp
  obtain ⟨n₁, h₁⟩ := code_size_even Q₁
  obtain ⟨n₂, h₂⟩ := code_size_even Q₂
  obtain ⟨n₃, h₃⟩ := code_size_even Q₃
  refine ⟨nX, n₁, n₂, n₃, by omega, by omega, by omega, by omega, ?_⟩
  simp only [RegCpl.size, RegChain.size] at hsz
  omega

theorem tc2_wf {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
    (hwf : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).wf = true) :
    Xp.wf = true ∧ (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true := by
  simp only [RegCpl.wf, Bool.and_eq_true] at hwf ⊢
  exact ⟨hwf.1.1.1.1, hwf.1.1.2⟩

variable {LG : LayeredGarden 2} {Xp : RegChain} {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2}
  (D : T2mData LG Xp LGX LGQ)
include D

theorem tc2_embX : PieceEmb D.gd.ι₁ (fun x => D.gd.ofSum (.inl x)) :=
  ⟨fun x => D.gd.ofSum_inl_toNode x, fun x i => D.gd.ofSum_inl_child x i⟩

theorem tc2_embQ : PieceEmb D.gd.ι₂ (fun y => D.gd.ofSum (.inr y)) :=
  ⟨fun y => D.gd.ofSum_inr_toNode y, fun y i => D.gd.ofSum_inr_child y i⟩

theorem tc2_hroot (hdec : ∀ t : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree t).branching)
    (S : Finset (GNode LG.garden.tree)) : ∀ a ∈ S, a.1.2 = [] → a.1.2 ∈ (LG.garden.tree a.1.1).branching := by
  intro a _ h0
  rw [h0]
  exact hdec a.1.1

/-- **The gate-form multiplier splits through the glue.** -/
theorem tc2_mult (hr : ∀ t : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree t).branching) {d : ℕ}
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (K : GNode LG.garden.tree → Mom d) :
    gateM S ω F M Fu Mu K =
      pullMult D.gd.ι₁ (fun x => D.gd.ofSum (.inl x)) S ω F M Fu Mu (K ∘ D.gd.ι₁) *
        pullMult D.gd.ι₂ (fun y => D.gd.ofSum (.inr y)) S ω F M Fu Mu (K ∘ D.gd.ι₂) := by
  have e : gateM S ω F M Fu Mu K = ∏ b, fD3' S ω F (fun _ => false) M Fu Mu b (bstar K b) :=
    starFilt_local' S (tc2_hroot D hr S) ω F (fun _ => false) M Fu Mu K
  rw [e, D.multGlue_local, pull_mult (tc2_embX D), pull_mult (tc2_embQ D)]
  rfl

/-- **The star cost splits through the glue.** -/
theorem tc2_cost (hr : ∀ t : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree t).branching)
    (S : Finset (GNode LG.garden.tree)) (cω : GNode LG.garden.tree → ℝ) :
    starCost S cω = starCost (pullS D.gd.ι₁ S) (fun z => cω (D.gd.ι₁ z)) *
      starCost (pullS D.gd.ι₂ S) (fun z => cω (D.gd.ι₂ z)) := by
  unfold starCost
  rw [prod_cost_branch S (tc2_hroot D hr S) cω, D.gd.prod_branch, pull_cost (tc2_embX D),
    pull_cost (tc2_embQ D)]

/-- The leaf bounds of the two pieces. -/
def tc2BX (B : (Fin 2 × TTree.Path) → NNReal) : (Fin 1 × TTree.Path) → NNReal := fun a => B (topAddr a)

/-- The leaf bounds of the lone-pair couple. -/
def tc2BQ (Xp : RegChain) (B : (Fin 2 × TTree.Path) → NNReal) : (Fin 2 × TTree.Path) → NNReal :=
  fun a => B (botAddr Xp.lonePath a)

omit D in
theorem tc2BX_def (B : (Fin 2 × TTree.Path) → NNReal) (a : Fin 1 × TTree.Path) : tc2BX B a = B (topAddr a) := rfl

theorem tc2_leafwise {d : ℕ} {H : LeafProfiles 2 d} {B : (Fin 2 × TTree.Path) → NNReal}
    (hH : LeafwiseControlled LG H B) :
    LeafwiseControlled LGX (t2HX H) (tc2BX B) ∧ LeafwiseControlled LGQ (t2HQ Xp H) (tc2BQ Xp B) := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.hm₁ D.hmtop ℓ hℓ
    have h1 : t2HX H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
    have h2 : tc2BX B ℓ.1 = B ℓ'.1 := by rw [he]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofBot D.hmbot ℓ hℓ
    have h1 : t2HQ Xp H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
    have h2 : tc2BQ Xp B ℓ.1 = B ℓ'.1 := by rw [he]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'

theorem tc2_leafSize (B : (Fin 2 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = leafSizeProduct LGX (tc2BX B) * leafSizeProduct LGQ (tc2BQ Xp B) := by
  unfold leafSizeProduct
  exact D.gd.prod_inputLeaves_glue D.hm₁ D.hmtop D.hmbot (fun a => (B a : ℝ))

theorem tc2_layerAt_X (x : Fin 1 × TTree.Path) (hx : x.2 ∈ (LGX.garden.tree x.1).nodes) :
    layerAt LGX x = layerAt LG (topAddr x) :=
  (layerAt_node LGX (⟨x, hx⟩ : GNode LGX.garden.tree)).trans (D.layX _)

theorem tc2_layerAt_Q (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LGQ.garden.tree x.1).nodes) :
    layerAt LGQ x = layerAt LG (botAddr Xp.lonePath x) :=
  (layerAt_node LGQ (⟨x, hx⟩ : GNode LGQ.garden.tree)).trans (D.layQ _)

theorem tc2_sigX {Qlp : RegCpl} (hdec : (RegCpl.type2 Xp .nil Qlp).Decodes LG.garden) : LGX.garden.sig 0 = 1 := by
  rw [D.gd.sig1, hdec.1.2]; rfl

/-- **The incoherency splits** into the chain tree and the lone-pair couple. -/
theorem tc2_incoh {Qlp : RegCpl} (hdec : (RegCpl.type2 Xp .nil Qlp).Decodes LG.garden)
    (hdQ : Qlp.Decodes LGQ.garden) :
    LG.incoherency (RegCpl.type2 Xp .nil Qlp).links =
      LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) + LGQ.incoherency Qlp.links := by
  classical
  have hs0 : LG.garden.sig 0 = 1 := by rw [hdec.1.2]; rfl
  have hsX : LGX.garden.sig 0 = 1 := D.gd.sig1.trans hs0
  set P : (Fin 2 × TTree.Path) × (Fin 2 × TTree.Path) → Bool := fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)
  rw [incoherency_eq_count hdec, tree_incoherency_eq_count D.decX, incoherency_eq_count hdQ]
  -- the chain
  have hX : (Xp.linksAt 1 ((0 : Fin 2), ([] : TTree.Path))).filter P =
      ((Xp.treeLinks (LGX.garden.sig 0)).filter (fun l => layerAt LGX l.1 ≠ layerAt LGX l.2)).map
        (fun l => (topAddr l.1, topAddr l.2)) := by
    have e0 : ((0 : Fin 2), ([] : TTree.Path)) = topAddr ((0 : Fin 1), []) := rfl
    rw [e0, chain_linksAt_map Xp topAddr (fun x q => topAddr_hom x q), RegChain.treeLinks, hsX, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have h1 := (tree_mem_pairEndpoints_links_iff D.decX l.1).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, hsX]; exact hl, Or.inl rfl⟩)
    have h2 := (tree_mem_pairEndpoints_links_iff D.decX l.2).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, hsX]; exact hl, Or.inr rfl⟩)
    simp only [Function.comp_apply, P]
    rw [tc2_layerAt_X D l.1 (TTree.branching_subset_nodes _ h1), tc2_layerAt_X D l.2 (TTree.branching_subset_nodes _ h2)]
  -- the lone-pair couple
  have hQ : (Qlp.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) Xp.lonePath)
        (addrExt ((1 : Fin 2), ([] : TTree.Path)) RegChain.nil.lonePath)).filter P =
      ((Qlp.links).filter (fun l => layerAt LGQ l.1 ≠ layerAt LGQ l.2)).map
        (fun l => (botAddr Xp.lonePath l.1, botAddr Xp.lonePath l.2)) := by
    have e0 : addrExt ((0 : Fin 2), ([] : TTree.Path)) Xp.lonePath = botAddr Xp.lonePath ((0 : Fin 2), []) := by
      simp [addrExt, botAddr]
    have e1 : addrExt ((1 : Fin 2), ([] : TTree.Path)) RegChain.nil.lonePath = botAddr Xp.lonePath ((1 : Fin 2), []) := by
      simp [addrExt, botAddr, RegChain.lonePath]
    rw [e0, e1, couple_linksAt_map Qlp (botAddr Xp.lonePath) (botAddr_hom Xp.lonePath), RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching hdQ hl
    simp only [Function.comp_apply, P]
    rw [tc2_layerAt_Q D l.1 (TTree.branching_subset_nodes _ hb.1),
      tc2_layerAt_Q D l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  have hL : (RegCpl.type2 Xp .nil Qlp).links = Xp.linksAt 1 ((0 : Fin 2), ([] : TTree.Path)) ++
      Qlp.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) Xp.lonePath)
        (addrExt ((1 : Fin 2), ([] : TTree.Path)) RegChain.nil.lonePath) := by
    simp [RegCpl.links, RegCpl.linksAt, RegChain.linksAt]
  rw [hL, List.filter_append, List.length_append]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)) (Xp.linksAt 1 ((0 : Fin 2), [])) =
    (Xp.linksAt 1 ((0 : Fin 2), [])).filter P from rfl, hX]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qlp.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) Xp.lonePath)
        (addrExt ((1 : Fin 2), ([] : TTree.Path)) RegChain.nil.lonePath)) =
      (Qlp.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) Xp.lonePath)
        (addrExt ((1 : Fin 2), ([] : TTree.Path)) RegChain.nil.lonePath)).filter P from rfl, hQ]
  simp only [List.length_map]

/-! ### The ambient of the pieces -/

/-- Layers of the couple read in a signed ambient. -/
theorem tc2_layH {w' : ℕ} {H : LayeredGarden w'} {a b : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2))
    (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes) :
    layerAt LG x = layerAt H (addrExt (if x.1 = 0 then a else b) x.2) :=
  (layerAt_node LG (⟨x, hx⟩ : GNode LG.garden.tree)).trans (hlay _)

/-- **The chain tree is a coherent tree object** (when coherent), parent layer `p`, lone layer `𝔏''`. -/
theorem tc2_treeCoh {p : ℕ} {Qlp : RegCpl} (hdec : (RegCpl.type2 Xp .nil Qlp).Decodes LG.garden)
    (hwX : Xp.wf = true) (hA : TcCplAmbS p (RegCpl.type2 Xp .nil Qlp) LG)
    (h0 : LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) = 0) :
    IsCoherentTreeAt p p (layerAt LG ((0 : Fin 2), Xp.lonePath)) Xp LGX := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, -, hpa, -, hlay⟩ := hA
  obtain ⟨hX, -, hQ⟩ := hE.type2
  have hsX := tc2_sigX D hdec
  have hlX : ∀ z : GNode LGX.garden.tree, LGX.layer z = layerAt H (addrExt a z.1.2) := by
    intro z
    have hm : z.1.2 ∈ (LG.garden.tree 0).nodes := by
      have h2 := z.2
      rw [show z.1.1 = 0 from Subsingleton.elim _ _] at h2
      exact D.gd.top_node h2
    rw [D.layX, tc2_layH D hlay ((0 : Fin 2), z.1.2) hm]
    simp
  have hlp : Xp.lonePath ∈ (LG.garden.tree 0).nodes := by
    have := (D.gd.bot_iff ((0 : Fin 2), [])).1.2 (TTree.nil_mem_nodes _)
    simpa [botAddr] using this
  refine ⟨hwX, D.decX, w', H, a, Qlp.trees.1, hcan, by rw [hsX]; exact hX, by rw [hsX, hsa],
    cohOn_of_tree D.decX hlX h0, hpa, ?_, hlX⟩
  rw [tc2_layH D hlay ((0 : Fin 2), Xp.lonePath) hlp]
  simp

/-- **The lone-pair couple in the signed ambient.** -/
theorem tc2_cplAmbQ {p : ℕ} {Qlp : RegCpl} (hA : TcCplAmbS p (RegCpl.type2 Xp .nil Qlp) LG) :
    ∃ (w' : ℕ) (H : LayeredGarden w') (a' b' : Fin w' × TTree.Path), IsCanonGC (p + 1) H ∧
      Embeds H.garden Qlp a' b' ∧ nodeSign H.garden.sig a' = 1 ∧ nodeSign H.garden.sig b' = -1 ∧
      ∀ z : GNode LGQ.garden.tree, LGQ.layer z = layerAt H (addrExt (if z.1.1 = 0 then a' else b') z.1.2) := by
  obtain ⟨w', H, a, b, hcan, hE, hsa, hsb, -, -, hlay⟩ := hA
  obtain ⟨-, -, hQ⟩ := hE.type2
  have eb : addrExt b RegChain.nil.lonePath = b := by simp [addrExt, RegChain.lonePath]
  rw [eb] at hQ
  refine ⟨w', H, addrExt a Xp.lonePath, b, hcan, hQ, by rw [nodeSign_spine, hsa], hsb, fun z => ?_⟩
  have hm := (D.gd.bot_iff z.1).1.2 z.2
  rw [D.layQ, tc2_layH D hlay _ hm]
  rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
  · simp [botAddr, hz, addrExt]
  · simp [botAddr, hz, addrExt]

end WaveTurbulence.Flower.ProtPin
