/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2mKer

/-! # D2c-3 PROT-CUT: the pieces of o104 Prop 7.4 (c) exist; branch-local multipliers factor

* `isLayering_pullbackW`: a layering pulled back along an address map (any widths).
* **`T2mData.exists_of_decodes`**: a well-formed `type2 Xp nil (type1 c Q₁ Q₂ Q₃)` decoding a layered couple `LG`
  has its chain `LGX` and lone-pair couple `LGQ` with the layers of `LG`; `T1Data.exists_of_decodes` then gives the
  sub-couples of `LGQ`.
* **`T2mData.multFactors_local`**: `K ↦ ∏_b f b (bstar K b)` satisfies the hypotheses `hMg` (glue) and `hMQ`
  (`T1Data.MultFactors` of `Q_lp`) of `kernelProt_t2m`, with explicit factors. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- A layering pulled back along an address map that sends branching nodes to branching nodes. -/
theorem isLayering_pullbackW {w w' : ℕ} (LG : LayeredGarden w) (G' : Garden w')
    (φ : Fin w' × Path → Fin w × Path) (hφ : ∀ x q, φ (addrExt x q) = addrExt (φ x) q)
    (hb : ∀ x : GBranch G'.tree, (φ x.1).2 ∈ (LG.garden.tree (φ x.1).1).branching)
    (hpair : ∀ ℓ : GLeaf G'.tree, layerAt LG (φ ℓ.1) = layerAt LG (φ (G'.pair ℓ).1)) :
    IsLayering G' (fun z => layerAt LG (φ z.1)) := by
  refine ⟨fun b i => ?_, hpair⟩
  let B : GBranch LG.garden.tree := ⟨φ b.1, hb b⟩
  have h := LG.isLayering.1 B i
  have e1 : layerAt LG (φ (b.child i).1) = LG.layer (B.child i) := by
    rw [← layerAt_node]
    exact congrArg (layerAt LG) (hφ b.1 [i])
  have e2 : layerAt LG (φ b.toNode.1) = LG.layer B.toNode := layerAt_node LG B.toNode
  show layerAt LG (φ (b.child i).1) ≤ layerAt LG (φ b.toNode.1)
  rw [e1, e2]
  exact h

/-- **The pieces of a type-2 couple with an empty `-` chain exist**, with the layers of the couple. -/
theorem T2mData.exists_of_decodes (LG : LayeredGarden 2) (Xp : RegChain) (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    (hd : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden)
    (hwf : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).wf = true) :
    ∃ (LGX : LayeredGarden 1) (LGQ : LayeredGarden 2), T2mData LG Xp LGX LGQ ∧
      (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes LGQ.garden := by
  simp only [RegCpl.wf, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨hwX, -⟩, hwQ⟩, -⟩, -⟩ := hwf
  obtain ⟨GX, hsX, hdX, -⟩ := Reg.wf_chain_exists_regular_decodesTree Xp hwX 1
  have hwQ' : (RegCpl.type1 c Q₁ Q₂ Q₃).wf = true := by simp only [RegCpl.wf, Bool.and_eq_true]; exact hwQ
  obtain ⟨GQ, hdQ, -⟩ := Reg.wf_code_exists_regular_decodes _ hwQ'
  have hd' : (RegCpl.type2 (appendChain Xp .nil) .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden := by
    rw [appendChain_nil_right]; exact hd
  have hdQ' : (SourceApp.closeCouple .nil .nil (.type1 c Q₁ Q₂ Q₃)).Decodes GQ := by
    rw [closeCouple_nil_nil]; exact hdQ
  have gd := glueData_couple hd' hdX hsX hdQ'
  have hpair : ∀ ℓ : GLeaf GX.tree, layerAt LG (topAddr ℓ.1) = layerAt LG (topAddr (GX.pair ℓ).1) := by
    intro ℓ
    by_cases hl : ℓ.1.2 = Xp.lonePath
    · have hm : GX.mark ℓ ≠ none := by rw [hdX.2.1 ℓ]; simp [hl]
      rw [(GX.pair_eq_iff ℓ).2 hm]
    · have hm := hdX.2.2 ℓ hl
      rw [mem_symmPairs] at hm
      have key : ∀ u v : Fin 1 × Path, (u, v) ∈ Xp.pairsAt (GX.sig 0) ((0 : Fin 1), []) →
          layerAt LG (topAddr u) = layerAt LG (topAddr v) := by
        intro u v huv
        refine layer_eq_of_decoded_pair hd (p := (topAddr u, topAddr v)) ?_
        simp only [RegCpl.pairsAt, List.mem_append]
        left; left
        have e := chain_pairsAt_map Xp (topAddr (w := 2)) (topAddr_hom (w := 2)) 1 ((0 : Fin 1), [])
        rw [hsX] at huv
        have : (topAddr u, topAddr v) ∈ Xp.pairsAt 1 (topAddr (w := 2) ((0 : Fin 1), [])) := by
          rw [e]; exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
        exact this
      rcases hm with hm | hm
      · exact key _ _ hm
      · exact (key _ _ hm).symm
  refine ⟨⟨GX, fun z => layerAt LG (topAddr z.1), isLayering_pullbackW LG GX topAddr (topAddr_hom (w := 2))
      (fun x => gd.branch_ofTop x) hpair⟩, botLayered_couple hd' hdX hsX hdQ',
    T2mData.of_decodes hd hdX hsX hdQ (fun z => rfl) (fun z => (layerAt_node LG (gd.ι₂ z)).symm), hdQ⟩

namespace T2mData

variable {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
  {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
  {LG₁ LG₂ LG₃ : LayeredGarden 2} (h : T1Data c Q₁ Q₂ Q₃ LGQ.garden LG₁.garden LG₂.garden LG₃.garden)
include D h

end T2mData

end WaveTurbulence.Flower.ProtCut
