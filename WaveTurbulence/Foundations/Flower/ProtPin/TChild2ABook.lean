/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.HelperA

/-! # D3-HELPER (P7), shape (a+): bookkeeping of a type-2 couple with a nonempty `+` chain

`Q = type2 (pair m Qr Qg inner rest) Xm Qlp` decoding `LG` (D2c's `Root2Data LG m Qr Qg inner LGZ LGB`: the closing
pair `LGZ` glued on the rest couple `LGB`, code `closeCouple rest Xm Qlp`; `PairOnly LGZ …`: the interior `LGi`, the
side couples `LGr`, `LGg`):

* `tc2a_exists`: the pieces exist, with the decoding of the rest couple (`Root2Data` does not record it);
* sizes and well-formedness (`tc2a_sizes`, `tc2a_wf`);
* the input leaves and the leaf-size product (`tc2a_leafwise`, `tc2a_leafSize`);
* the placed pieces as `PieceEmb`s and the branch product of the couple (`tc2a_prod_branch`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-! ### Existence (D2c's `Root2Data.exists_of_decodes`, recording the rest-couple decoding) -/

/-- **The pieces of a type-2 couple with a nonempty `+` chain exist**, with the decoding of the rest couple. -/
theorem tc2a_exists (LG : LayeredGarden 2) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest Xm : RegChain)
    (Qlp : RegCpl) (hd : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).Decodes LG.garden)
    (hwf : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).wf = true) :
    ∃ (LGZ : LayeredGarden 1) (LGB : LayeredGarden 2), Root2Data LG m Qr Qg inner LGZ LGB ∧
      (cpair m Qr Qg inner).wf = true ∧ (SourceApp.closeCouple rest Xm Qlp).wf = true ∧
      (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden ∧ LGZ.garden.sig 0 = 1 := by
  have hwf' : (RegCpl.type2 (appendChain (cpair m Qr Qg inner) rest) Xm Qlp).wf = true := hwf
  obtain ⟨hwZ, hwB⟩ := wf_split hwf'
  have hd' : (RegCpl.type2 (appendChain (cpair m Qr Qg inner) rest) Xm Qlp).Decodes LG.garden := hd
  obtain ⟨GZ, hsZ, hdZ, -⟩ := Reg.wf_chain_exists_regular_decodesTree _ hwZ 1
  obtain ⟨GB, hdB, -⟩ := Reg.wf_code_exists_regular_decodes _ hwB
  have gd := glueData_couple hd' hdZ hsZ hdB
  have hpair : ∀ ℓ : GLeaf GZ.tree, layerAt LG (topAddr ℓ.1) = layerAt LG (topAddr (GZ.pair ℓ).1) := by
    intro ℓ
    by_cases hl : ℓ.1.2 = (cpair m Qr Qg inner).lonePath
    · have hm : GZ.mark ℓ ≠ none := by rw [hdZ.2.1 ℓ]; simp [hl]
      rw [(GZ.pair_eq_iff ℓ).2 hm]
    · have hm := hdZ.2.2 ℓ hl
      rw [mem_symmPairs] at hm
      have key : ∀ u v : Fin 1 × Path, (u, v) ∈ (cpair m Qr Qg inner).pairsAt (GZ.sig 0) ((0 : Fin 1), []) →
          layerAt LG (topAddr u) = layerAt LG (topAddr v) := by
        intro u v huv
        refine layer_eq_of_decoded_pair hd (p := (topAddr u, topAddr v)) ?_
        have e := chain_pairsAt_map (cpair m Qr Qg inner) (topAddr (w := 2)) (topAddr_hom (w := 2)) 1
          ((0 : Fin 1), [])
        rw [hsZ] at huv
        have hin : (topAddr u, topAddr v) ∈
            (cpair m Qr Qg inner).pairsAt 1 (topAddr (w := 2) ((0 : Fin 1), [])) := by
          rw [e]; exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
        have hin' : (topAddr u, topAddr v) ∈ (RegChain.pair m Qr Qg inner rest).pairsAt 1 ((0 : Fin 2), []) := by
          rw [show topAddr (w := 2) ((0 : Fin 1), ([] : Path)) = ((0 : Fin 2), []) from rfl] at hin
          simp only [RegChain.pairsAt, List.mem_append, List.not_mem_nil, or_false] at hin ⊢
          tauto
        simp only [RegCpl.pairsAt, List.mem_append]
        left; left; exact hin'
      rcases hm with hm | hm
      · exact key _ _ hm
      · exact (key _ _ hm).symm
  exact ⟨⟨GZ, fun z => layerAt LG (topAddr z.1), isLayering_pullbackW LG GZ topAddr (topAddr_hom (w := 2))
      (fun x => gd.branch_ofTop x) hpair⟩, botLayered_couple hd' hdZ hsZ hdB,
    Root2Data.of_decodes hd hdZ hsZ hdB (fun z => rfl) (fun z => (layerAt_node LG (gd.ι₂ z)).symm), hwZ, hwB, hdB,
    hsZ⟩

/-! ### Sizes, well-formedness -/

theorem tc2a_closeCouple_size (rest Xm : RegChain) (Qlp : RegCpl) :
    (SourceApp.closeCouple rest Xm Qlp).size = rest.size + Xm.size + Qlp.size := by
  unfold SourceApp.closeCouple
  cases rest <;> cases Xm <;> simp [RegChain.isNil, RegCpl.size, RegChain.size]

theorem tc2a_sizes {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest Xm : RegChain} {Qlp : RegCpl} {n : ℕ}
    (hsz : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).size = 2 * n) :
    ∃ nB nI nR nG : ℕ, (SourceApp.closeCouple rest Xm Qlp).size = 2 * nB ∧ inner.size = 2 * nI ∧
      Qr.size = 2 * nR ∧ Qg.size = 2 * nG ∧ nB + nI + nR + nG + 1 = n := by
  obtain ⟨nB, hB⟩ := code_size_even (SourceApp.closeCouple rest Xm Qlp)
  obtain ⟨nI, hI⟩ := chain_size_even inner
  obtain ⟨nR, hR⟩ := code_size_even Qr
  obtain ⟨nG, hG⟩ := code_size_even Qg
  refine ⟨nB, nI, nR, nG, by omega, by omega, by omega, by omega, ?_⟩
  have e := tc2a_closeCouple_size rest Xm Qlp
  simp only [RegCpl.size, RegChain.size] at hsz
  omega

theorem tc2a_wf {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest Xm : RegChain} {Qlp : RegCpl}
    (hwf : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).wf = true) :
    inner.wf = true ∧ Qr.wf = true ∧ Qg.wf = true ∧ (SourceApp.closeCouple rest Xm Qlp).wf = true := by
  have hwf' : (RegCpl.type2 (appendChain (cpair m Qr Qg inner) rest) Xm Qlp).wf = true := hwf
  obtain ⟨hwZ, hwB⟩ := wf_split hwf'
  simp only [RegChain.wf, Bool.and_eq_true] at hwZ
  exact ⟨hwZ.1.2, hwZ.1.1.1, hwZ.1.1.2, hwB⟩

/-! ### Leaves -/

/-- Leaf bounds of the rest couple. -/
def tc2aBB (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (B : (Fin 2 × TTree.Path) → NNReal) :
    (Fin 2 × TTree.Path) → NNReal := fun a => B (botAddr (cpair m Qr Qg inner).lonePath a)

/-- Leaf bounds of the interior. -/
def tc2aBI (m : MiniTreeCode) (B : (Fin 2 × TTree.Path) → NNReal) : (Fin 1 × TTree.Path) → NNReal :=
  fun a => B ((0 : Fin 2), m.c :: a.2)

/-- Leaf bounds of the red couple. -/
def tc2aBR (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (B : (Fin 2 × TTree.Path) → NNReal) :
    (Fin 2 × TTree.Path) → NNReal := fun a => B ((0 : Fin 2), rBase m inner ζ a.1 ++ a.2)

/-- Leaf bounds of the green couple. -/
def tc2aBG (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (B : (Fin 2 × TTree.Path) → NNReal) :
    (Fin 2 × TTree.Path) → NNReal := fun a => B ((0 : Fin 2), gBase m inner ζ a.1 ++ a.2)

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D

theorem tc2a_inLeafZ (ℓ : GLeaf LGZ.garden.tree) (hℓ : ℓ ∈ inputLeaves LGZ.garden) :
    ∃ ℓ' ∈ inputLeaves LG.garden, ℓ'.1 = topAddr ℓ.1 :=
  D.gd.inputLeaf_ofTop (fun ℓ => D.decZ.2.1 ℓ) (fun ℓ _ => D.plain ℓ) ℓ hℓ

theorem tc2a_inLeafB (ℓ : GLeaf LGB.garden.tree) (hℓ : ℓ ∈ inputLeaves LGB.garden) :
    ∃ ℓ' ∈ inputLeaves LG.garden, ℓ'.1 = botAddr (cpair m Qr Qg inner).lonePath ℓ.1 :=
  D.gd.inputLeaf_ofBot (fun ℓ₂ ℓ _ => by rw [D.plain ℓ, D.plainB ℓ₂]) ℓ hℓ

include P

/-- **The leaf control of the four pieces.** -/
theorem tc2a_leafwise {d : ℕ} {H : LeafProfiles 2 d} {B : (Fin 2 × TTree.Path) → NNReal}
    (hH : LeafwiseControlled LG H B) :
    LeafwiseControlled LGB (t2HQ (cpair m Qr Qg inner) H) (tc2aBB m Qr Qg inner B) ∧
    LeafwiseControlled LGi (cutHi .nil m (t2HX H)) (tc2aBI m B) ∧
    LeafwiseControlled LGr (cutHr .nil m inner (LGZ.garden.sig 0) (t2HX H)) (tc2aBR m inner (LGZ.garden.sig 0) B) ∧
    LeafwiseControlled LGg (cutHg .nil m inner (LGZ.garden.sig 0) (t2HX H)) (tc2aBG m inner (LGZ.garden.sig 0) B) := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨ℓ', hℓ', he⟩ := tc2a_inLeafB D ℓ hℓ
    have h1 : t2HQ (cpair m Qr Qg inner) H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
    have h2 : tc2aBB m Qr Qg inner B ℓ.1 = B ℓ'.1 := by rw [he]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := P.hp.inputLeaf_ofI ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := tc2a_inLeafZ D ℓ₁ hℓ₁
    have e : ((0 : Fin 2), m.c :: ℓ.1.2) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφi]
    have h1 : cutHi .nil m (t2HX H) ℓ.1 = H ℓ'.1 := by
      rw [← e]; simp [cutHi, t2HX, topAddr, RegChain.lonePath]
    have h2 : tc2aBI m B ℓ.1 = B ℓ'.1 := by rw [← e]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := P.hp.inputLeaf_ofR ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := tc2a_inLeafZ D ℓ₁ hℓ₁
    have e : ((0 : Fin 2), rBase m inner (LGZ.garden.sig 0) ℓ.1.1 ++ ℓ.1.2) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφr]
    have h1 : cutHr .nil m inner (LGZ.garden.sig 0) (t2HX H) ℓ.1 = H ℓ'.1 := by
      rw [← e]; simp [cutHr, t2HX, topAddr, RegChain.lonePath]
    have h2 : tc2aBR m inner (LGZ.garden.sig 0) B ℓ.1 = B ℓ'.1 := by rw [← e]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'
  · obtain ⟨ℓ₁, hℓ₁, he₁⟩ := P.hp.inputLeaf_ofG ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := tc2a_inLeafZ D ℓ₁ hℓ₁
    have e : ((0 : Fin 2), gBase m inner (LGZ.garden.sig 0) ℓ.1.1 ++ ℓ.1.2) = ℓ'.1 := by
      rw [he, he₁]; simp [topAddr, pφg]
    have h1 : cutHg .nil m inner (LGZ.garden.sig 0) (t2HX H) ℓ.1 = H ℓ'.1 := by
      rw [← e]; simp [cutHg, t2HX, topAddr, RegChain.lonePath]
    have h2 : tc2aBG m inner (LGZ.garden.sig 0) B ℓ.1 = B ℓ'.1 := by rw [← e]; rfl
    rw [h1, h2]
    exact hH ℓ' hℓ'

/-- **The leaf-size product splits** over the four pieces. -/
theorem tc2a_leafSize (B : (Fin 2 × TTree.Path) → NNReal) :
    leafSizeProduct LG B = leafSizeProduct LGB (tc2aBB m Qr Qg inner B) *
      (leafSizeProduct LGi (tc2aBI m B) * leafSizeProduct LGr (tc2aBR m inner (LGZ.garden.sig 0) B) *
        leafSizeProduct LGg (tc2aBG m inner (LGZ.garden.sig 0) B)) := by
  set f : Fin 2 × TTree.Path → ℝ := fun z => (B z : ℝ) with hf
  have e0 : leafSizeProduct LG B = ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := rfl
  rw [e0, D.gd.prod_inputLeaves_glue (fun ℓ => D.decZ.2.1 ℓ) (fun ℓ _ => D.plain ℓ)
    (fun ℓ₂ ℓ _ => by rw [D.plain ℓ, D.plainB ℓ₂]) f,
    P.hp.prod_inputLeaves_pair (fun z => f (topAddr z))]
  have e1 : ∏ ℓ ∈ inputLeaves LGB.garden, f (botAddr (cpair m Qr Qg inner).lonePath ℓ.1) =
      leafSizeProduct LGB (tc2aBB m Qr Qg inner B) := rfl
  have e2 : ∏ ℓ ∈ inputLeaves LGi.garden, f (topAddr (pφi m ℓ.1)) = leafSizeProduct LGi (tc2aBI m B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφi, tc2aBI]
  have e3 : ∏ ℓ ∈ inputLeaves LGr.garden, f (topAddr (pφr m inner (LGZ.garden.sig 0) ℓ.1)) =
      leafSizeProduct LGr (tc2aBR m inner (LGZ.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφr, tc2aBR]
  have e4 : ∏ ℓ ∈ inputLeaves LGg.garden, f (topAddr (pφg m inner (LGZ.garden.sig 0) ℓ.1)) =
      leafSizeProduct LGg (tc2aBG m inner (LGZ.garden.sig 0) B) := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [hf, topAddr, pφg, tc2aBG]
  rw [e1, e2, e3, e4]
  ring

/-! ### The placed pieces -/

omit P in
theorem tc2a_embZ : PieceEmb D.gd.ι₁ (fun x => D.gd.ofSum (.inl x)) :=
  ⟨fun _ => rfl, fun x i => D.gd.ofSum_inl_child x i⟩

omit P in
theorem tc2a_embB : PieceEmb D.gd.ι₂ (fun y => D.gd.ofSum (.inr y)) :=
  ⟨fun y => D.gd.ofSum_inr_toNode y, fun y i => D.gd.ofSum_inr_child y i⟩

theorem tc2a_embI : PieceEmb (fun z => D.gd.ι₁ (P.hp.ιi z)) (fun x => D.gd.ofSum (.inl (P.hp.βi x))) :=
  (⟨P.hp.βi_toNode, P.hp.βi_child⟩ : PieceEmb P.hp.ιi P.hp.βi).comp (tc2a_embZ D)

theorem tc2a_embR : PieceEmb (fun z => D.gd.ι₁ (P.hp.ιr z)) (fun y => D.gd.ofSum (.inl (P.hp.βr y))) :=
  (⟨P.hp.βr_toNode, P.hp.βr_child⟩ : PieceEmb P.hp.ιr P.hp.βr).comp (tc2a_embZ D)

theorem tc2a_embG : PieceEmb (fun z => D.gd.ι₁ (P.hp.ιg z)) (fun y => D.gd.ofSum (.inl (P.hp.βg y))) :=
  (⟨P.hp.βg_toNode, P.hp.βg_child⟩ : PieceEmb P.hp.ιg P.hp.βg).comp (tc2a_embZ D)

/-- **The branches of the couple**: the two linked nodes, the rest couple, the interior and the side couples. -/
theorem tc2a_prod_branch {α : Type*} [CommMonoid α] (φ : GBranch LG.garden.tree → α) :
    ∏ b, φ b = φ (D.aR P) * φ (D.bR P) * ((∏ y, φ (D.gd.ofSum (.inr y))) *
      ((∏ x, φ (D.gd.ofSum (.inl (P.hp.βi x)))) * ((∏ y, φ (D.gd.ofSum (.inl (P.hp.βr y)))) *
        ∏ y, φ (D.gd.ofSum (.inl (P.hp.βg y)))))) := by
  rw [D.gd.prod_branch, P.hp.prod_pairBranch (fun x => φ (D.gd.ofSum (.inl x)))]
  unfold Root2Data.aR Root2Data.bR
  ac_rfl

end Data

end WaveTurbulence.Flower.ProtPin
