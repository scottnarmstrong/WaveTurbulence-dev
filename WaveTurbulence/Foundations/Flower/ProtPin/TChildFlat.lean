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

variable {LG LGp LGi : LayeredGarden 1} {LGr' LGg' : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

end WaveTurbulence.Flower.ProtPin
