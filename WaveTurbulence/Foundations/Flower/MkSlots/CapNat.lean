/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapGeoQ

/-! # B3s MK-SLOTS (cap slots): the native kernel of a nontrivial cap slot is a `term` protected kernel

For a nontrivial cap slot (`CapSide`) of a reconstruction with capped geometry (`CapGeo … J p`):
* the chain is a D2b stem chain of the reconstruction (`capStem`), whose lone leaf is the capped flower;
* the paired tree `T1` of the native cap couple is D2b's `objTree` of the reconstruction (`capT1_layer`,
  `capT1_eq`), hence a protected object (`ProtShape`, `ProtAmbient`);
* the intrinsic plain pins `fixCap … plain`, read on the native couple, are the `term` pins of `T1` (`capFix`),
  and they have a free parent (`capPins`: the capped flower parent is never the top of the chain, `X ≠ nil`);
* **`capSlot_kernel`**: the pinned slot kernel `slotFnNWF … (.inl q) ts k` is the `term`-pinned protected kernel
  of `T1` at the upper clock `ts j0` (`capTermKer`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- The attachment address of the chain. -/
abbrev u : Fin w × Path := inflatedPosition S D.tree K.leaf.toNode

/-- The native cap couple as a D6b cap couple. -/
def Dq : CapG (nativeCoupleLayered D hS layer hLayer q) K.j0 K.c K.X K.ζ :=
  K.capG _ (nativeCoupleLayered_garden D hS layer hLayer q)

/-- The capped flower: the lone leaf of the chain in the reconstruction. -/
def flower : GLeaf (D.garden hS).tree :=
  ⟨addrExt K.u K.X.lonePath, (node_iff_of_subtree K.emb.node K.emb.tree K.X.lonePath).2.1.2
    (PL234.lonePath_mem_leaves K.X K.ζ)⟩

theorem isCapFlower : IsCapFlower (layeredReconstruction D hS layer hLayer) J K.flower := by
  refine ⟨?_, ?_⟩
  · show (addrExt K.u K.X.lonePath).1 ∉ J
    show (inflatedPosition S D.tree K.leaf.toNode).1 ∉ J
    rw [inflatedPosition_index]
    exact K.lJ
  · show ((D.garden hS).pair K.flower).1.1 ∈ J
    rw [K.lone K.flower rfl, inflatedPosition_index]
    exact K.cJ

/-- **The chain of a nontrivial cap slot is a D2b stem chain of the reconstruction.** -/
theorem capStem : StemChain (layeredReconstruction D hS layer hLayer) J K.X K.ζ K.u .leaf := by
  refine ⟨K.emb, K.wf, ?_⟩
  have hb := prefix_lone_branching K.X K.ζ (List.dropLast_prefix K.X.lonePath) (dropLast_lonePath_ne K.ne)
  refine ⟨embBr K.emb _ hb, addrExt_mem_branchAddresses.2 hb, K.flower, K.isCapFlower layer hLayer, rfl, ?_⟩
  show (K.u.2 ++ K.X.lonePath.dropLast) <+: (K.u.2 ++ K.X.lonePath)
  exact (List.prefix_append_right_inj _).2 (List.dropLast_prefix _)

theorem portFlower : PortFlower (layeredReconstruction D hS layer hLayer) J K.X K.u :=
  ⟨K.flower, K.isCapFlower layer hLayer, rfl⟩

/-! ### The paired tree is the reconstruction's `objTree` -/

theorem emb_ι (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    ((nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1)).1 = addrExt K.u a1.1.2 := by
  show (((nativeCoupleForest D hS q).root K.j0).1.1, ((nativeCoupleForest D hS q).root K.j0).1.2 ++ a1.1.2) = _
  rw [K.root_j0]
  rfl

theorem mem_nodes_ι (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    (addrExt K.u a1.1.2).2 ∈ ((D.garden hS).tree (addrExt K.u a1.1.2).1).nodes := by
  have h := ((nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1)).2
  rw [K.emb_ι layer hLayer a1] at h
  exact h

theorem capT1_layer (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    (K.Dq layer hLayer).T1.layer a1 = layerAt (layeredReconstruction D hS layer hLayer) (addrExt K.u a1.1.2) := by
  rw [layerAt_of_mem (layeredReconstruction D hS layer hLayer) (K.mem_nodes_ι layer hLayer a1),
    ← (K.Dq layer hLayer).layer_ι]
  show layer ((nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1)) = _
  congr 1
  exact Subtype.ext (K.emb_ι layer hLayer a1)

theorem capT1_eq : (K.Dq layer hLayer).T1 = objTree (layeredReconstruction D hS layer hLayer) K.X K.ζ K.u K.emb := by
  show objTree (nativeCoupleLayered D hS layer hLayer q) K.X K.ζ (K.j0, []) (K.Dq layer hLayer).emb = _
  unfold objTree
  congr 1
  funext a1
  exact K.capT1_layer layer hLayer a1

/-! ### The pins -/

variable {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

end CapSide

end WaveTurbulence.Flower.MkSlots
