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

theorem term_fix_eq (X : RegChain) (s t up : ℝ) {T : Fin 1 → TTree} (b1 : GBranch T) :
    ProtCfg.term.fix X s t up b1 = if b1.1.2 = X.lonePath.dropLast then some s else none := by
  unfold ProtCfg.fix
  rw [if_pos (Fin.val_eq_zero b1.1.1)]
  simp only [ProtCfg.pins, List.lookup]
  by_cases h : b1.1.2 = X.lonePath.dropLast
  · simp [h]
  · rw [beq_false_of_ne h, if_neg h]

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

theorem objCfg_plain :
    objCfg (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) K.X K.u = .term := by
  unfold objCfg
  simp [K.portFlower layer hLayer]

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

include hGeo in
/-- **The intrinsic plain pins on the paired tree are the `term` pins.** -/
theorem capFix (t s up : ℝ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q)
      ((K.Dq layer hLayer).βc b1) = ProtCfg.term.fix K.X s t up b1 := by
  have hb : subforestBranchEmbedding (nativeCoupleForest D hS q) ((K.Dq layer hLayer).βc b1) =
      embBr (K.capStem layer hLayer).emb b1.1.2 b1.2 := by
    refine Subtype.ext ?_
    show (((nativeCoupleForest D hS q).root K.j0).1.1, ((nativeCoupleForest D hS q).root K.j0).1.2 ++ b1.1.2) = _
    rw [K.root_j0]
    rfl
  show fixCap (layeredReconstruction D hS layer hLayer) J _ t s
    (subforestBranchEmbedding (nativeCoupleForest D hS q) ((K.Dq layer hLayer).βc b1)) = _
  rw [hb, fixCap_objTree hGeo (K.capStem layer hLayer) _ t s up b1, K.objCfg_plain layer hLayer]
  rfl

include hGeo in
theorem capFix_eq (t s up : ℝ) (b : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree) :
    fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q) b =
      if b.1.2 = K.X.lonePath.dropLast then some s else none := by
  have hb : b = (K.Dq layer hLayer).βc ((K.Dq layer hLayer).βc.symm b) := (Equiv.apply_symm_apply _ b).symm
  rw [hb, K.capFix layer hLayer hGeo t s up, term_fix_eq]
  rfl

include K hGeo in
/-- **The pins of a nontrivial cap slot have a free parent.** -/
theorem capPins (t s : ℝ) (hps : (p : ℝ) < s) (hsp : s < p + 1) (up : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree → ℝ)
    (hup : ∀ b b', up b = up b') :
    CapPins (nativeCoupleLayered D hS layer hLayer q) up
      (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q)) := by
  set Dq := K.Dq layer hLayer
  have hfix := K.capFix_eq layer hLayer hGeo t s 0
  have hpin : ∀ (b : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree) (v : ℝ),
      fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s)
      (.inl q) b = some v → b.1.2 = K.X.lonePath.dropLast ∧ v = s := by
    intro b v hb
    rw [hfix] at hb
    by_cases h : b.1.2 = K.X.lonePath.dropLast
    · rw [if_pos h] at hb
      exact ⟨h, (Option.some.inj hb).symm⟩
    · rw [if_neg h] at hb
      exact absurd hb (by simp)
  refine ⟨fun b v hb => ?_, fun b v hb => ?_, fun b b' hbb' => ?_, fun b => Dq.not_loneParent b⟩
  · obtain ⟨h, rfl⟩ := hpin b v hb
    obtain ⟨b1, rfl⟩ := Dq.βc.surjective b
    have hl : (nativeCoupleLayered D hS layer hLayer q).layer (Dq.βc b1).toNode = p := by
      rw [Dq.βc_toNode, Dq.layer_ι, K.capT1_layer layer hLayer]
      have hq : b1.1.2 = K.X.lonePath.dropLast := h
      show layerAt (layeredReconstruction D hS layer hLayer) (addrExt K.u b1.1.2) = p
      rw [hq]
      exact (K.capStem layer hLayer).chain_layer hGeo (List.dropLast_prefix _) (dropLast_lonePath_ne K.ne)
    rw [hl]
    exact ⟨hps, hsp, lt_of_le_of_lt (Nat.cast_nonneg p) hps⟩
  · obtain ⟨h, -⟩ := hpin b v hb
    obtain ⟨b1, rfl⟩ := Dq.βc.surjective b
    have hpre : K.X.lonePath.dropLast.dropLast <+: K.X.lonePath :=
      (List.dropLast_prefix _).trans (List.dropLast_prefix _)
    have hne : K.X.lonePath.dropLast.dropLast ≠ K.X.lonePath := by
      intro he
      have := congrArg List.length he
      simp only [List.length_dropLast] at this
      have := two_le_lonePath K.ne
      omega
    have hbr := prefix_lone_branching K.X K.ζ hpre hne
    let b1' : GBranch Dq.T1.garden.tree := ⟨((0 : Fin 1), K.X.lonePath.dropLast.dropLast), hbr⟩
    refine ⟨Dq.βc b1', ⟨rfl, ?_⟩, ?_, le_of_eq (hup _ _)⟩
    · refine ⟨K.X.lonePath.dropLast.getLast (dropLast_lonePath_ne_nil K.ne), ?_⟩
      rw [h]
      exact (List.dropLast_append_getLast _).symm
    · rw [hfix, if_neg]
      intro he
      have h3 : (Dq.βc b1').1.2 = K.X.lonePath.dropLast.dropLast := rfl
      rw [h3] at he
      have := congrArg List.length he
      simp only [List.length_dropLast] at this
      have := two_le_lonePath K.ne
      omega
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨v1, hv1⟩ := Option.ne_none_iff_exists'.1 h1
    obtain ⟨v2, hv2⟩ := Option.ne_none_iff_exists'.1 h2
    obtain ⟨e1, -⟩ := hpin b v1 hv1
    obtain ⟨e2, -⟩ := hpin b' v2 hv2
    obtain ⟨-, i, hi⟩ := hbb'
    have := congrArg List.length hi
    rw [e1, e2] at this
    simp at this

end CapSide

end WaveTurbulence.Flower.MkSlots
