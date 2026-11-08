/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Flat
public import WaveTurbulence.Foundations.Flower.ProtPin.Pieces

/-! # D3 PROT-PIN: the coherent pieces of the terminal cut are flat in layer `p`

For a protected paired tree `X = Xp ++ pair m Qr Qg inner nil` with its canonical ambient (`TreeAmb`; R172), D2c's four
pieces (prefix `Xp`, interior `inner`, side couples `Qr`, `Qg`) are placed both in the object (main's
`ChainEmb.of_decodesTree`, `chainEmb_append_left/right`, `ChainEmb.parts`) and in the ambient `H` (the same lemmas,
D0's `protAmbient_termCut`). Their roots and lone positions are the partner nodes `𝔫_a`, `𝔫_b` or stem nodes, all in
layer `p` (`ChainIn`), so each coherent piece is flat in layer `p` (`flat_tree_sub`, `side_flat`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Links WaveTurbulence.Reg Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}

/-- **The coherent pieces of the terminal cut are flat in layer `p`.** -/
theorem cut_flat (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {p : ℕ}
    (hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
    (hA : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    (LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) = 0 → ∀ z, LGp.layer z = p) ∧
    (LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 → ∀ z, LGi.layer z = p) ∧
    (LGr.incoherency Qr.links = 0 → ∀ z, LGr.layer z = p) ∧
    (LGg.incoherency Qg.links = 0 → ∀ z, LGg.layer z = p) := by
  obtain ⟨w', H, a, h, hcan, hC, hlay⟩ := hA
  have hch := hsh.2.2.2
  obtain ⟨hwfp, hwfi, hwfr, hwfg⟩ := cut_wf D hsh.1
  obtain ⟨hlp, hlonep, hli, hlonei, -, -⟩ := cut_layers D hsh
  -- the pieces in the object
  have hCL := ChainEmb.of_decodesTree D.dec
  have hCLp := PL234.chainEmb_append_left hCL
  have hCLz := PL234.chainEmb_append_right hCL
  obtain ⟨hrL, hgL, hiL, -⟩ := hCLz.parts
  -- the pieces in the ambient
  have hCp := PL234.chainEmb_append_left hC
  have hCz := PL234.chainEmb_append_right hC
  obtain ⟨hr, hg, hi, -⟩ := hCz.parts
  -- the partner nodes are in layer `p`
  have hstem := stem_layer D.dec hch hlay
  have hlpX : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ ([m.c] ++ inner.lonePath ++ [m.lone]) := by
    rw [appendChain_lonePath]
    simp [RegChain.lonePath]
  have hxa : layerAt H (addrExt a Xp.lonePath) = p :=
    hstem _ (by rw [hlpX]; exact List.prefix_append _ _) (by rw [hlpX]; simp)
  have hxb : layerAt H (addrExt a (Xp.lonePath ++ ([m.c] ++ inner.lonePath))) = p :=
    hstem _ (by rw [hlpX]; exact ⟨[m.lone], by simp⟩) (by rw [hlpX]; simp)
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · -- the prefix
    exact flat_tree_sub hcan hlay hwfp D.decP (r := ((0 : Fin 1), [])) (by rw [D.sigP]; exact hCLp)
      (by rw [D.sigP]; exact hCp) (by simp [addrExt]) (fun z => by rw [D.layP z]; simp [addrExt]) hlp hlonep h0
  · -- the interior chain
    exact flat_tree_sub hcan hlay hwfi D.decI (by rw [D.sigI]; exact hiL) (by rw [D.sigI]; exact hi)
      (by simp [addrExt]) (fun z => by rw [D.layI z]; simp [addrExt]) hli hlonei h0
  · -- the red side couple
    exact side_flat hcan hlay hwfr D.decR Xp.lonePath ([m.c] ++ inner.lonePath) m.red.1 m.red.2
      (slotSign (LG.garden.sig 0) m.red.1) (rBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [rBase, hs], by simp [rBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [rBase, hs, bPath], by simp [rBase, hs]⟩) hrL hr D.layR hxa hxb h0
  · -- the green side couple
    exact side_flat hcan hlay hwfg D.decG Xp.lonePath ([m.c] ++ inner.lonePath) m.green.1 m.green.2
      (slotSign (LG.garden.sig 0) m.green.1) (gBase m inner (LG.garden.sig 0))
      (fun hs => ⟨by simp [gBase, hs], by simp [gBase, hs, bPath]⟩)
      (fun hs => ⟨by simp [gBase, hs, bPath], by simp [gBase, hs]⟩) hgL hg D.layG hxa hxb h0

end WaveTurbulence.Flower.ProtPin
