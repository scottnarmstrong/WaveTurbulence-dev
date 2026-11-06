/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoherentSlices

/-!
# Every node of a same-layer block is in that layer (TARGET L1236–L1237)

TARGET L1237: "all the nodes in `𝒯_{[r]}` except the lone leaf are in layer `r`". For an embedded chain
with the coherent layer pattern of LAYERREG (`ChainPairLayers`: the two nodes of each pair and its two
couples are in one layer):

* `chainNodes_layer_of_ends`: if the root and the lone position are in layer `r`, every node is (layers do
  not increase from a node to its descendants, so the spine is sandwiched);
* `chainNodes_layer_of_topAll`: if every top-level pair is in layer `r` (a block, `takeLayer`), every node
  is.
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {w : ℕ}

/-- Every top-level pair of the chain is in layer `r`. -/
def TopAll (LG : LayeredGarden w) (r : ℕ) : (Fin w × Path) → RegChain → Prop
  | _, .nil => True
  | a, .pair m _ _ inner rest => layerAt LG a = r ∧ TopAll LG r (nextAddr a m inner) rest

theorem topAll_takeLayer (LG : LayeredGarden w) (r : ℕ) :
    ∀ (a : Fin w × Path) (X : RegChain), TopAll LG r a (takeLayer LG a r X)
  | _, .nil => trivial
  | a, .pair m Qr Qg inner rest => by
    unfold takeLayer
    split_ifs with h
    · exact ⟨h, topAll_takeLayer LG r _ rest⟩
    · trivial

theorem layer_sandwich {LG : LayeredGarden w} {x y z : Fin w × Path} {r : ℕ}
    (hx : x.2 ∈ (LG.garden.tree x.1).nodes) (hy : y.2 ∈ (LG.garden.tree y.1).nodes)
    (hz : z.2 ∈ (LG.garden.tree z.1).nodes) (hxy : Under x y) (hyz : Under y z)
    (hlx : layerAt LG x = r) (hlz : layerAt LG z = r) : layerAt LG y = r :=
  le_antisymm ((layerAt_le_of_under LG hx hy hxy).trans hlx.le)
    (hlz.symm.le.trans (layerAt_le_of_under LG hy hz hyz))

/-- **A chain whose root and lone position are in layer `r` lies in layer `r`.** -/
theorem chainNodes_layer_of_ends {LG : LayeredGarden w} {r : ℕ} :
    ∀ {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}, ChainEmb LG.garden X ζ a h →
      ChainPairLayers LG X ζ a → layerAt LG a = r → layerAt LG (addrExt a X.lonePath) = r →
      ∀ z ∈ chainNodesSet X ζ a, layerAt LG z = r
  | .nil, _, _, _, _, _, _, _ => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt]
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, ha, hlone => by
    obtain ⟨hb, hr, hg, hi, hs⟩ := hL
    obtain ⟨-, -, hCi, hCr⟩ := hC.parts
    have nA := hC.node
    have nLone := nodeOfChainEmb hC
    have nI := hCi.node
    have nB := nodeOfChainEmb hCi
    have nR := hCr.node
    have nRl := nodeOfChainEmb hCr
    have eB : addrExt (addrExt a [m.c]) inner.lonePath = addrExt a ([m.c] ++ inner.lonePath) :=
      addrExt_append _ _ _
    have eR : addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath =
        addrExt a (RegChain.pair m Qr Qg inner rest).lonePath := by
      rw [addrExt_append]
      simp [RegChain.lonePath, List.append_assoc]
    rw [eB] at nB
    rw [eR] at nRl
    have lB : layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) = r := hb.trans ha
    have lI : layerAt LG (addrExt a [m.c]) = r :=
      layer_sandwich nA nI nB (under_ext a _) (by
        rw [← eB]; exact under_ext _ _) ha lB
    have lR : layerAt LG (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) = r :=
      layer_sandwich (z := addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) nB nR nLone
        ((under_ext_iff a _ _).mpr (List.prefix_append _ _)) (by rw [← eR]; exact under_ext _ _) lB hlone
    intro z hz
    rcases mem_chainNodesSet_pair hz with rfl | rfl | hz | hz | hz | hz
    · exact ha
    · exact lB
    · exact (hr z hz).trans ha
    · exact (hg z hz).trans ha
    · exact chainNodes_layer_of_ends hCi hi lI (by rw [eB]; exact lB) z hz
    · exact chainNodes_layer_of_ends hCr hs lR (by rw [eR]; exact hlone) z hz

/-- **Every node of a same-layer block is in that layer.** -/
theorem chainNodes_layer_of_topAll {LG : LayeredGarden w} {r : ℕ} :
    ∀ {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}, ChainEmb LG.garden X ζ a h →
      ChainPairLayers LG X ζ a → TopAll LG r a X → ∀ z ∈ chainNodesSet X ζ a, layerAt LG z = r
  | .nil, _, _, _, _, _, _ => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt]
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, ⟨ha, hT⟩ => by
    obtain ⟨hb, hr, hg, hi, hs⟩ := hL
    obtain ⟨-, -, hCi, hCr⟩ := hC.parts
    have nA := hC.node
    have nI := hCi.node
    have nB := nodeOfChainEmb hCi
    have eB : addrExt (addrExt a [m.c]) inner.lonePath = addrExt a ([m.c] ++ inner.lonePath) :=
      addrExt_append _ _ _
    rw [eB] at nB
    have lB : layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) = r := hb.trans ha
    have lI : layerAt LG (addrExt a [m.c]) = r :=
      layer_sandwich nA nI nB (under_ext a _) (by rw [← eB]; exact under_ext _ _) ha lB
    intro z hz
    rcases mem_chainNodesSet_pair hz with rfl | rfl | hz | hz | hz | hz
    · exact ha
    · exact lB
    · exact (hr z hz).trans ha
    · exact (hg z hz).trans ha
    · exact chainNodes_layer_of_ends hCi hi lI (by rw [eB]; exact lB) z hz
    · exact chainNodes_layer_of_topAll hCr hs hT z hz

end WaveTurbulence.PL234
