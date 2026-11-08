/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapNat

/-! # B3s MK-SLOTS (cap slots): the slot kernel identity and the profiles of the paired tree

* **`capSlot_kernel`**: the pinned slot kernel `slotFnNWF … (.inl q) ts k` of a nontrivial cap slot is the
  `term`-pinned protected kernel of the paired tree at the upper clock `ts j0` (`capTermKer`), with the cap pair's
  leaf factors in the multiplier;
* `capH1_leafwise`: the paired tree's profiles (the anchored profiles of the reconstruction at its non-lone leaves,
  which are not anchored) are leafwise controlled by the profile bound;
* `capPairFactor_one`: at the cap momentum, the cap pair's anchored factors are `1` on every coset decoration. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine

namespace WaveTurbulence.Flower.MkSlots

namespace CapSide

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-- The profiles of the native couple, as leaf profiles. -/
abbrev Hq {d : ℕ} (H : LeafProfiles w d) : LeafProfiles 2 d :=
  capProfiles (nativeCoupleLayered D hS layer hLayer q) (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)

omit K in
theorem Hq_def {d : ℕ} (H : LeafProfiles w d) :
    Hq (q := q) layer hLayer H = capProfiles (nativeCoupleLayered D hS layer hLayer q)
      (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1) := rfl

/-- The multiplier of the paired tree. -/
def m1 {d : ℕ} (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) : ℂ :=
  (∏ a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree,
      W ((nativeCoupleForest D hS q).nodeEmbedding a) (K' ((K.Dq layer hLayer).ρ a))) *
    CapG.capPairFactor (K.Dq layer hLayer) (Hq (q := q) layer hLayer H) K'

theorem up_βc (ts : Fin 2 → ℝ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    (fun b : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree => if b.1.1 = 0 then ts 0 else ts 1)
      ((K.Dq layer hLayer).βc b1) = ts K.j0 := by
  show (if K.j0 = 0 then ts 0 else ts 1) = ts K.j0
  by_cases h : K.j0 = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    have : K.j0 = 1 := by omega
    rw [this]

include hGeo in
/-- **The slot kernel identity.** -/
theorem capSlot_kernel {d : ℕ} (L γ δ : ℝ) (t s : ℝ) (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFnNWF D hS L γ δ H W layer hLayer
        (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q) ts k =
      capTermKer L γ δ (K.Dq layer hLayer) (CapG.capH1 K.j0 (Hq (q := q) layer hLayer H)) (K.m1 layer hLayer H W) s t k
        (ts K.j0) := by
  set Dq := K.Dq layer hLayer
  set up : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree → ℝ :=
    fun b => if b.1.1 = 0 then ts 0 else ts 1 with hupdef
  have hup : ∀ b b', up b = up b' := by
    intro b b'
    show (if b.1.1 = 0 then ts 0 else ts 1) = (if b'.1.1 = 0 then ts 0 else ts 1)
    rw [Dq.branch_j0 b, Dq.branch_j0 b']
  show kernelNodeWF L γ δ (nativeCoupleLayered D hS layer hLayer q)
      (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) up 0 k (fun _ => 0) 0
      (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) (.inl q)) = _
  refine (kernelNodeWF_eq_kernelProt L γ δ _ _ _ up k _ _ _ (K.capPins layer hLayer hGeo t s hps hsp up hup)).trans
    ((CapG.kernelProt_capG_T1 Dq L γ δ _ _ up _ k).trans ?_)
  unfold capTermKer
  have hu : (fun b => up (Dq.βc b)) = fun _ => ts K.j0 := funext fun b1 => K.up_βc layer hLayer ts b1
  have hf : (fun b => fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s)
      (.inl q) (Dq.βc b)) = ProtCfg.term.fix K.X s t (ts K.j0) :=
    funext fun b1 => K.capFix layer hLayer hGeo t s (ts K.j0) b1
  rw [hu, hf]
  rfl

/-! ### Profiles -/

theorem Hq_ι {d : ℕ} (H : LeafProfiles w d) (a1 : GNode (K.Dq layer hLayer).T1.garden.tree) :
    CapG.capH1 K.j0 (Hq (q := q) layer hLayer H) a1.1 = H (addrExt K.u a1.1.2) := by
  unfold CapG.capH1 Hq capProfiles
  split_ifs with hm
  · show H ((nativeCoupleForest D hS q).nodeEmbedding ((K.Dq layer hLayer).ι a1)).1 = _
    rw [K.emb_ι layer hLayer a1]
  · exact absurd ((K.Dq layer hLayer).ι a1).2 hm

include hGeo in
theorem capH1_leafwise {d : ℕ} (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (b : ℝ)
    (hb0 : 0 ≤ b) (hb : ∀ q' ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q' j j') ≤ ENNReal.ofReal b) :
    LeafwiseControlled (K.Dq layer hLayer).T1
      (CapG.capH1 K.j0 (Hq (q := q) layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)))
      (fun _ => b.toNNReal) := by
  intro ℓ hℓ
  have hne : ℓ.1.2 ≠ K.X.lonePath := ((K.Dq layer hLayer).mark1_iff ℓ).1 (Finset.mem_filter.1 hℓ).2.2
  have hH := K.Hq_ι layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots) ℓ.toNode
  change SNormR (40 * d) (40 * d) (CapG.capH1 K.j0 (Hq (q := q) layer hLayer
    (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)) ℓ.toNode.1) ≤ _
  rw [hH]
  set G := layeredReconstruction D hS layer hLayer
  have hleaf : (addrExt K.u ℓ.1.2).2 ∈ (G.garden.tree (addrExt K.u ℓ.1.2).1).leaves :=
    (node_iff_of_subtree K.emb.node K.emb.tree ℓ.1.2).2.1.2 ℓ.2
  let e : GLeaf G.garden.tree := ⟨addrExt K.u ℓ.1.2, hleaf⟩
  have hp := objTree_pair (LG := G) K.emb ℓ hne e rfl
  have h1 : e.1.1 = K.u.1 := rfl
  have h2 : (G.garden.pair e).1.1 = K.u.1 := by rw [hp]; rfl
  have huJ : K.u.1 ∉ J := by
    show (inflatedPosition S D.tree K.leaf.toNode).1 ∉ J
    rw [inflatedPosition_index]; exact K.lJ
  show SNormR (40 * d) (40 * d) (anchProfiles J G h L roots e.1) ≤ _
  unfold anchProfiles
  rw [pairTrees_leaf, h1, h2, if_neg huJ, if_neg huJ, typeProfiles_leaf G h e, h1, h2]
  rw [Real.coe_toNNReal b hb0]
  exact hb _ (hGeo.layer_le _) _ _

end CapSide

end WaveTurbulence.Flower.MkSlots
