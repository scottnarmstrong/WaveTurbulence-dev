/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1TT1
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2m

/-! # RT-GATE (ii), fork C: the (c−) pieces in the windowed ambient

For `Q = type2 Xp nil Qlp` traced at the root of tree `1` (the root of `Qlp`, window `p`) with the partner (tree `0`,
the chain tree `Xp`) in the window `q'` (`MkSlotsO.CplAmbient p q' p`):
* `rt1t_treeCoh`: the chain tree, when coherent, is a coherent tree of the ambient with parent layer `q'`;
* `rt1t_cplAmbQ`: the lone-pair couple `Qlp` in the raw signed ambient (D3's `tc2_cplAmbQ`, no parent layers). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem rt1t_rpow4 {L : ℝ} (hL : 0 < L) (c' : ℝ) : L ^ c' * L ^ c' * L ^ c' * L ^ c' = L ^ (4 * c') := by
  rw [show 4 * c' = c' + c' + c' + c' by ring, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL]

section Data

variable {LG : LayeredGarden 2} {Xp : RegChain} {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2}
  (D : T2mData LG Xp LGX LGQ)
include D

/-- **The chain tree is a coherent tree object** (when coherent), parent layer `q'`, lone layer `𝔏''`. -/
theorem rt1t_treeCoh {p q' : ℕ} {Qlp : RegCpl} (hdec : (RegCpl.type2 Xp .nil Qlp).Decodes LG.garden)
    (hwX : Xp.wf = true) (hA : MkSlotsO.CplAmbient p q' p (RegCpl.type2 Xp .nil Qlp) LG)
    (h0 : LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) = 0) :
    IsCoherentTreeAt p q' (layerAt LG ((0 : Fin 2), Xp.lonePath)) Xp LGX := by
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
theorem rt1t_cplAmbQ {p q₀ q₁ : ℕ} {Qlp : RegCpl} (hA : MkSlotsO.CplAmbient p q₀ q₁ (RegCpl.type2 Xp .nil Qlp) LG) :
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

end Data

end WaveTurbulence.Flower.ProtRT
