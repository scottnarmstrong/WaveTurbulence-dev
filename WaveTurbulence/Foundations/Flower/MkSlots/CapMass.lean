/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMul3
public import WaveTurbulence.Foundations.Flower.ProtPin.Ambient
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegSum

/-! # B3s MK-SLOTS (cap slots): clock and mass bookkeeping of a nontrivial cap slot

* `clk_j0`, `slotBox_j0`: the chain clock of the slot box is in the window `[p, p + 1]` (the parent of the
  chain's root is on the capped stem);
* `protShape_T1`, `protAmbient_T1`: the paired tree is a D3 protected object;
* `protIncoh_T1`: its incoherency is the slot incoherency; `frontS_card_le`: its frontier nodes are garden
  non-roots of the slot; `leafSize_T1_le`: its leaf size is `b⁻¹` times the slot's leaf size. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-! ### The clock -/

include hGeo in
theorem clk_j0 : Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode)
    (Represents.argSrc hS (.inl q) K.j0) = p := by
  rw [K.arg, ← Represents.parentLayer_inflated D hS layer hLayer p K.leaf.toNode ⟨K.u, K.emb.node⟩ rfl]
  unfold LayeredGarden.parentLayer
  split_ifs with h
  · rfl
  · refine hGeo.stem_layer _ ⟨K.flower, K.isCapFlower layer hLayer, rfl, ?_⟩
    show K.u.2.dropLast <+: K.u.2 ++ K.X.lonePath
    exact (List.dropLast_prefix _).trans (List.prefix_append _ _)

include hGeo in
theorem slotBox_j0 (ts : Fin 2 → ℝ)
    (hts : ts ∈ Represents.slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS (.inl q)) :
    ts K.j0 ∈ Set.Icc (p : ℝ) (p + 1) := by
  have hc := K.clk_j0 layer hLayer hGeo
  obtain ⟨h0, h1⟩ := hts
  by_cases hj : K.j0 = 0
  · rw [hj] at hc ⊢
    have := h0
    rw [hc] at this
    exact this
  · have hj1 : K.j0 = 1 := by omega
    rw [hj1] at hc ⊢
    have := h1
    rw [hc] at this
    exact this

/-! ### The paired tree is a protected object -/

include hGeo in
theorem protShape_T1 : ProtShape p K.X (K.Dq layer hLayer).T1 := by
  rw [K.capT1_eq layer hLayer]
  exact protShape_objTree hGeo (K.capStem layer hLayer)

theorem protAmbient_T1 (hcan : IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer)) :
    ProtAmbient p K.X (K.Dq layer hLayer).T1 := by
  rw [K.capT1_eq layer hLayer]
  refine ProtPin.protAmbient_objTree hcan K.emb ?_
  show nodeSign S.sig (inflatedPosition S D.tree K.leaf.toNode) = K.ζ
  rw [inflatedPosition_sign]
  exact K.sign

theorem protIncoh_T1 :
    protIncoh K.X (K.Dq layer hLayer).T1 = Represents.slotIncoh D hS layer hLayer (.inl q) := by
  have hQ : (D.couple q).Decodes (nativeCoupleLayered D hS layer hLayer q).garden := by
    rw [nativeCoupleLayered_garden]; exact decodedCouple_decodes _
  exact (K.Dq layer hLayer).protIncoh_eq hQ K.links

theorem slotSize_eq : Represents.slotSize D (.inl q) = K.X.size := K.size

theorem two_le_size : 2 ≤ K.X.size := by
  have h := K.ne
  cases hX : K.X with
  | nil => exact absurd hX h
  | pair m Qr Qg inner rest => simp [RegChain.size]

/-! ### Frontier count and leaf size -/

theorem frontS_card_le : (K.frontS layer hLayer p).card ≤ Stage1WNoVine.slotNr D hS (.inl q) := by
  unfold Stage1WNoVine.slotNr
  refine Finset.card_le_card_of_injOn (fun a1 => (K.Dq layer hLayer).ι a1) (fun a1 ha1 => ?_) ?_
  · have h := (Finset.mem_filter.1 (Finset.mem_coe.1 ha1)).2
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.1⟩)
  · intro a1 _ b1 _ h
    have := congrArg (fun z : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree => z.1.2) h
    exact K.node_ext1 layer hLayer this

theorem leafSize_T1_le (b : ℝ) (hb : 1 ≤ b) :
    leafSizeProduct (K.Dq layer hLayer).T1 (fun _ => b.toNNReal) ≤
      b⁻¹ * Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q) := by
  set Dq := K.Dq layer hLayer
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb
  set LGq := nativeCoupleLayered D hS layer hLayer q
  -- the slot's leaf size is a power of `b`
  have hSL : Represents.slotLeaf D hS layer hLayer (fun _ => b.toNNReal) (.inl q) =
      b ^ (inputLeaves LGq.garden).card := by
    show leafSizeProduct LGq (Represents.nativeCoupleB D hS (fun _ => b.toNNReal) q) = _
    unfold leafSizeProduct
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((nativeCoupleGarden D hS q).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [Represents.nativeCoupleB, hn, ↓reduceDIte, Real.coe_toNNReal b hb0]
  have hT1 : leafSizeProduct Dq.T1 (fun _ => b.toNNReal) = b ^ (inputLeaves Dq.T1.garden).card := by
    unfold leafSizeProduct
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun _ _ => Real.coe_toNNReal b hb0
  rw [hSL, hT1]
  -- one member of the cap pair is an input leaf
  have hcard : (inputLeaves Dq.T1.garden).card + 1 ≤ (inputLeaves LGq.garden).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := inputLeaves LGq.garden)
      (CapG.IsCapPairLeaf K.c)
    have hneg : ((inputLeaves LGq.garden).filter (fun ℓ => ¬ CapG.IsCapPairLeaf K.c ℓ)).card =
        (inputLeaves Dq.T1.garden).card := by
      have h := congrArg Finset.card Dq.inputLeaves_filter
      rw [Finset.card_map] at h
      convert h using 2
    have hpos : 0 < ((inputLeaves LGq.garden).filter (CapG.IsCapPairLeaf K.c)).card := by
      refine Finset.card_pos.2 ?_
      -- the cap root and the capped flower have opposite signs
      have hleaf : ([] : Path) ∈ (LGq.garden.tree K.c).leaves := by rw [Dq.cap]; simp [TTree.leaves]
      let r : GLeaf LGq.garden.tree := ⟨(K.c, []), hleaf⟩
      have hpr : LGq.garden.pair r = Dq.ℓ0 := Dq.pair_c r rfl
      have hne : LGq.garden.pair r ≠ r := fun h => (LGq.garden.pair_eq_iff r).1 h (Dq.plain r)
      have hs := LGq.garden.pair_sign r hne
      have hcr : CapG.IsCapPairLeaf K.c r := Or.inl (Finset.mem_singleton_self _)
      have hc0 : CapG.IsCapPairLeaf K.c Dq.ℓ0 := Or.inr (by rw [Dq.pair_ℓ0]; exact Finset.mem_singleton_self _)
      rcases Int.units_eq_one_or (nodeSign LGq.garden.sig r.1) with h1 | h1
      · exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, Dq.plain r⟩, hcr⟩⟩
      · refine ⟨Dq.ℓ0, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, Dq.plain _⟩, hc0⟩⟩
        show nodeSign LGq.garden.sig Dq.ℓ0.1 = 1
        rw [← hpr, hs, h1]
        rfl
    omega
  have hpow : b ^ ((inputLeaves Dq.T1.garden).card + 1) ≤ b ^ (inputLeaves LGq.garden).card :=
    pow_le_pow_right₀ hb hcard
  rw [pow_succ] at hpow
  rw [le_inv_mul_iff₀ hbpos]
  linarith [hpow, mul_comm b (b ^ (inputLeaves Dq.T1.garden).card)]

end CapSide

end WaveTurbulence.Flower.MkSlots
