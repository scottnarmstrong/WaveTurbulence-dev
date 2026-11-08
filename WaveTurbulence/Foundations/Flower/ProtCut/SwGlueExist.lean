/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.SwGlue

/-! # D2c-3 PROT-CUT: the pieces of a couple with a chain on tree `1` exist

**`SwGlueData.exists_of_decodes`**: a well-formed `type2 X₂ (appendChain X Y) Qlp` decoding a layered couple `LG` has the
paired tree `LGX` of `X` (sign `-1`) and the rest couple `LGB` (`closeCouple X₂ Y Qlp`) with the layers of `LG` (read
along `top1`, `phiB`). Instances: o104 Prop 7.4 (a), `ε = -` (`X = cpair m Qr Qg inner`, `Y = rest`) and (c), `ε = +`
(`X = Xm`, `Y = X₂ = nil`; `appendChain Xm nil = Xm`, `appendChain_nil_right`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **The pieces of a couple with the chain `X` on top of tree `1` exist.** -/
theorem SwGlueData.exists_of_decodes (LG : LayeredGarden 2) (X₂ X Y : RegChain) (Qlp : RegCpl)
    (hd : (RegCpl.type2 X₂ (appendChain X Y) Qlp).Decodes LG.garden)
    (hwf : (RegCpl.type2 X₂ (appendChain X Y) Qlp).wf = true) :
    ∃ (LGX : LayeredGarden 1) (LGB : LayeredGarden 2), SwGlueData LG X₂ X Y Qlp LGX LGB := by
  have hwf' := hwf
  simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true', appendChain_wf] at hwf'
  obtain ⟨⟨⟨⟨hw₂, hwX, hwY⟩, hwQ⟩, ht⟩, -⟩ := hwf'
  obtain ⟨GX, hsX, hdX, -⟩ := Reg.wf_chain_exists_regular_decodesTree X hwX (-1)
  obtain ⟨GB, hdB, -⟩ := Reg.wf_code_exists_regular_decodes _ (closeCouple_wf hw₂ hwY hwQ ht)
  have gd := glueSw hd hdX hsX hdB
  set lp := X.lonePath
  have hsG : LG.garden.sig = ![1, -1] := hd.1.2
  -- the layers of the chain `X`
  have hpairX : ∀ ℓ : GLeaf GX.tree, layerAt LG (top1 ℓ.1) = layerAt LG (top1 (GX.pair ℓ).1) := by
    intro ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · have hm : GX.mark ℓ ≠ none := by rw [hdX.2.1 ℓ]; simp [hl]
      rw [(GX.pair_eq_iff ℓ).2 hm]
    · have hm := hdX.2.2 ℓ hl
      rw [mem_symmPairs] at hm
      have key : ∀ u v : Fin 1 × Path, (u, v) ∈ X.pairsAt (GX.sig 0) ((0 : Fin 1), []) →
          layerAt LG (top1 u) = layerAt LG (top1 v) := by
        intro u v huv
        refine layer_eq_of_decoded_pair hd (p := (top1 u, top1 v)) ?_
        have e := chain_pairsAt_map X top1 top1_hom (-1) ((0 : Fin 1), [])
        rw [hsX] at huv
        have hin : (top1 u, top1 v) ∈ X.pairsAt (-1) (top1 ((0 : Fin 1), [])) := by
          rw [e]; exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
        rw [show top1 ((0 : Fin 1), ([] : Path)) = ((1 : Fin 2), []) from rfl] at hin
        simp only [RegCpl.pairsAt, appendChain_pairsAt, List.mem_append]
        tauto
      rcases hm with hm | hm
      · exact key _ _ hm
      · exact (key _ _ hm).symm
  -- the layers of the rest couple
  have hbB : ∀ y : GBranch GB.tree, (phiB lp y.1).2 ∈ (LG.garden.tree (phiB lp y.1).1).branching := by
    rintro ⟨⟨t, p⟩, hy⟩
    have h1 := gd.branch_ofBot (brF ⟨(t, p), hy⟩)
    fin_cases t
    · exact h1
    · exact h1
  have hpairB : ∀ ℓ : GLeaf GB.tree, layerAt LG (phiB lp ℓ.1) = layerAt LG (phiB lp (GB.pair ℓ).1) := by
    intro ℓ
    have hm := hdB.2.2.2 ℓ
    rw [mem_symmPairs] at hm
    have key : ∀ u v : Fin 2 × Path, (u, v) ∈ (SourceApp.closeCouple X₂ Y Qlp).raw.2 →
        layerAt LG (phiB lp u) = layerAt LG (phiB lp v) := by
      intro u v huv
      refine layer_eq_of_decoded_pair hd (p := (phiB lp u, phiB lp v)) ?_
      have e := couple_pairsAt_map (SourceApp.closeCouple X₂ Y Qlp) (phiB lp) (phiB_hom lp)
        ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
      have e0 : phiB lp ((0 : Fin 2), ([] : Path)) = (0, []) := by simp [phiB]
      have e1 : phiB lp ((1 : Fin 2), ([] : Path)) = (1, lp) := by simp [phiB]
      rw [e0, e1, pairsAt_closeCouple] at e
      have hin : (phiB lp u, phiB lp v) ∈ (RegCpl.type2 X₂ Y Qlp).pairsAt (0, []) (1, lp) := by
        rw [e]
        exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
      simp only [RegCpl.pairsAt, appendChain_pairsAt, appendChain_lonePath, List.mem_append] at hin ⊢
      have e2 : addrExt ((1 : Fin 2), ([] : Path)) X.lonePath = (1, lp) := by simp [addrExt, lp]
      have e3 : addrExt ((1 : Fin 2), lp) Y.lonePath = addrExt ((1 : Fin 2), ([] : Path)) (X.lonePath ++ Y.lonePath) := by
        simp [addrExt, lp]
      rw [e2]
      rw [e3] at hin
      tauto
    rcases hm with hm | hm
    · exact key _ _ hm
    · exact (key _ _ hm).symm
  exact ⟨⟨GX, fun z => layerAt LG (top1 z.1), isLayering_pullbackW LG GX top1 top1_hom
      (fun x => gd.branch_ofTop x) hpairX⟩,
    ⟨GB, fun y => layerAt LG (phiB lp y.1), isLayering_pullbackW LG GB (phiB lp) (phiB_hom lp) hbB hpairB⟩,
    ⟨hd, hdX, hsX, hdB, fun _ => rfl, fun _ => rfl⟩⟩

/-- The `ε = +` instance of o104 Prop 7.4 (c): a couple decoded by `type2 nil Xm Qlp`. -/
theorem SwGlueData.exists_of_decodes_nil (LG : LayeredGarden 2) (Xm : RegChain) (Qlp : RegCpl)
    (hd : (RegCpl.type2 .nil Xm Qlp).Decodes LG.garden) (hwf : (RegCpl.type2 .nil Xm Qlp).wf = true) :
    ∃ (LGX : LayeredGarden 1) (LGB : LayeredGarden 2), SwGlueData LG .nil Xm .nil Qlp LGX LGB := by
  have hd' : (RegCpl.type2 .nil (appendChain Xm .nil) Qlp).Decodes LG.garden := by
    rw [appendChain_nil_right]; exact hd
  have hwf' : (RegCpl.type2 .nil (appendChain Xm .nil) Qlp).wf = true := by
    rw [appendChain_nil_right]; exact hwf
  exact SwGlueData.exists_of_decodes LG .nil Xm .nil Qlp hd' hwf'

end WaveTurbulence.Flower.ProtCut
