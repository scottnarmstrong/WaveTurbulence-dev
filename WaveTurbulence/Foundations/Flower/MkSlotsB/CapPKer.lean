/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeavesL
public import WaveTurbulence.Foundations.Flower.MkSlots.CapSlotN

/-! # B3s-HELPER3 (B5): the pattern cap slot kernel is D2a's protected kernel of the paired tree

Under R187 the relaxed slot kernel of a slot has no clock constraint at pinned branches (`slotFnGWFRL`): its domain is
`kDomainR … (fun _ => False) False = kDomainFix` (`kDomainR_eq_kDomainFix`), so on a native couple (no lone parents)
it IS D2a's protected kernel `kernelProt` (`kernelNodeWR_kDomainFix_eq_kernelProt`), with no side condition on the
pins. On a nontrivial cap slot (B3s's `CapSide`), D6b's `kernelProt_capG_T1` passes to the paired tree `T1`, and D2b's
`fixCap_objTree` reads the pattern pins `fixCap … pat` on `T1` as the pins of the configuration
`objCfg … pat X u` (`capFixPat`).

* `kernelNodeWR_kDomainFix_eq_kernelProt`;
* `capSlotKerPat` (the pattern cap slot kernel, relaxed, R187 form);
* `CapP.cfgPat`, `CapP.capFixPat`, **`CapP.capSlot_kernel_pat`**, `CapP.cfgKer_m1` (D3's multiplier, any pins),
  `CapP.objCfg_cases`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine WaveTurbulence.Flower.MkSlots WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Flower.ProtCut

namespace WaveTurbulence.Flower.MkSlotsB

/-- **A relaxed node kernel on `kDomainFix` is the protected kernel** (no lone parents, unit decoration weight). -/
theorem kernelNodeWR_kDomainFix_eq_kernelProt {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) (hl : ∀ b, ¬ LG.garden.IsLoneParent b) :
    kernelNodeWR L γ δ LG A m (kDomainFix LG up fix) k₀ nroot nfl (fun _ => 1) fix =
      kernelProt L γ δ LG (capProfiles LG A) m up 0 fix k₀ nroot nfl := by
  rw [kernelProt_eq_tsum]
  unfold kernelNodeWR
  congr 1
  refine tsum_congr fun κ => ?_
  unfold ProtCut.protSummand ProtCut.protTime ProtCut.protDom
  rw [mul_one]
  have hdom : kDomainFix LG up fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → (0 : ℝ) < τ b} =
      kDomainFix LG up fix := by
    ext τ
    exact ⟨fun h => h.1, fun h => ⟨h, fun b hb => absurd hb (hl b)⟩⟩
  rw [hdom]
  congr 2
  · congr 1
    rw [integral_fixMeasure]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    dsimp only
    rw [← capExtendFix_eq]
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [capProfiles_leaf]

/-- **The pattern cap slot kernel** (R187 form): the relaxed slot kernel `slotFnGWFRL` with the anchored profiles, the
capped node weight and the pattern pins `fixCap … pat`. -/
def capSlotKerPat {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) :
    ReplacementSlot a.prime.skeleton → (Fin 2 → ℝ) → Mom d → ℂ :=
  slotFnGWFRL a.prime.data a.prime.prime.1 L γ δ (anchProfiles J (recLG a) h L roots)
    (capNodeW L γ δ p s (recLG a) J Rf dag) (fun _ _ _ => 1) (sourceLayer a) (sourceLayer_isLayering a)
    (fixCap (recLG a) J pat t s)

namespace CapP

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-- The configuration of the paired tree under the pattern `pat` (D2b's `objCfg`). -/
abbrev cfgPat (pat : Fin w → FixPat) : ProtCfg :=
  objCfg (layeredReconstruction D hS layer hLayer) J pat K.X K.u

theorem objCfg_cases (pat : Fin w → FixPat) :
    cfgPat K layer hLayer pat = ProtCfg.term ∨ cfgPat K layer hLayer pat = ProtCfg.rootTerm ∨
      cfgPat K layer hLayer pat = ProtCfg.penTerm ∨ ∃ i, cfgPat K layer hLayer pat = ProtCfg.termChild i := by
  have hpf := K.portFlower layer hLayer
  unfold cfgPat objCfg
  cases pat K.u.1 with
  | plain => simp [hpf]
  | dRoot =>
    simp only [hpf, ite_true]
    split_ifs <;> simp
  | dParent =>
    simp only [hpf, ite_true]
    split_ifs <;> simp
  | dChild i =>
    simp only [hpf, ite_true]
    split_ifs <;> simp

include hGeo in
/-- **The pattern pins on the paired tree are the pins of `objCfg … pat`.** -/
theorem capFixPat (pat : Fin w → FixPat) (t s up : ℝ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) :
    fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ((K.Dq layer hLayer).βc b1) =
      (cfgPat K layer hLayer pat).fix K.X s t up b1 := by
  have hb : subforestBranchEmbedding (nativeCoupleForest D hS q) ((K.Dq layer hLayer).βc b1) =
      embBr (K.capStem layer hLayer).emb b1.1.2 b1.2 := by
    refine Subtype.ext ?_
    show (((nativeCoupleForest D hS q).root K.j0).1.1, ((nativeCoupleForest D hS q).root K.j0).1.2 ++ b1.1.2) = _
    rw [K.root_j0]
    rfl
  show fixCap (layeredReconstruction D hS layer hLayer) J pat t s
    (subforestBranchEmbedding (nativeCoupleForest D hS q) ((K.Dq layer hLayer).βc b1)) = _
  rw [hb, fixCap_objTree hGeo (K.capStem layer hLayer) pat t s up b1]
  rfl

include hGeo in
/-- **The pattern slot kernel identity** (R187): the relaxed slot kernel of a nontrivial cap slot is the protected
kernel of the paired tree at the upper clock `ts j0`, with the pins of `objCfg … pat`. -/
theorem capSlot_kernel_pat {d : ℕ} (L γ δ : ℝ) (pat : Fin w → FixPat) (t s : ℝ) (H : LeafProfiles w d)
    (W : GNode (D.forest hS) → Mom d → ℂ) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFnGWFRL D hS L γ δ H W (fun _ _ _ => 1) layer hLayer
        (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ts k =
      kernelProt L γ δ (K.Dq layer hLayer).T1 (CapG.capH1 K.j0 (MkSlots.CapSide.Hq (q := q) layer hLayer H)) (K.m1 layer hLayer H W)
        (fun _ => ts K.j0) 0 ((cfgPat K layer hLayer pat).fix K.X s t (ts K.j0)) k (fun _ => 0) 0 := by
  set Dq := K.Dq layer hLayer
  set up : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree → ℝ :=
    fun b => if b.1.1 = 0 then ts 0 else ts 1 with hupdef
  show kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer q)
      (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a))
      (kDomainR (nativeCoupleLayered D hS layer hLayer q) up 0
        (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)) (fun _ => False) False)
      k (fun _ => 0) 0 (fun _ => 1)
      (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)) = _
  have e := kDomainR_eq_kDomainFix (nativeCoupleLayered D hS layer hLayer q) up
    (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q))
  refine (congrArg (fun Dom => kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer q)
      (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) Dom k (fun _ => 0) 0 (fun _ => 1)
      (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q))) e).trans ?_
  refine (kernelNodeWR_kDomainFix_eq_kernelProt L γ δ _ _ _ up k _ _ _ Dq.not_loneParent).trans ?_
  refine (CapG.kernelProt_capG_T1 Dq L γ δ _ _ up _ k).trans ?_
  have hu : (fun b => up (Dq.βc b)) = fun _ => ts K.j0 := funext fun b1 => K.up_βc layer hLayer ts b1
  have hf : (fun b => fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)
      (Dq.βc b)) = (cfgPat K layer hLayer pat).fix K.X s t (ts K.j0) :=
    funext fun b1 => capFixPat K layer hLayer hGeo pat t s (ts K.j0) b1
  rw [hu, hf]
  rfl

include hGeo in
/-- D3's multiplier on the slot's protected kernel, for ANY pins. -/
theorem cfgKer_m1 {d : ℕ} (L γ δ s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (H1 : LeafProfiles 1 d)
    (up : GBranch (K.Dq layer hLayer).T1.garden.tree → ℝ) (s' : ℝ)
    (fix : GBranch (K.Dq layer hLayer).T1.garden.tree → Option ℝ) :
    kernelProt L γ δ (K.Dq layer hLayer).T1 H1
        (K.m1 layer hLayer (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
          (capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag)) up s' fix
        (latticePoint L (roots K.cleaf.1.1)) (fun _ => 0) 0 =
      K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
        kernelProt L γ δ (K.Dq layer hLayer).T1 H1
          (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
            (K.capInd layer hLayer dag K' : ℂ)) up s' fix (latticePoint L (roots K.cleaf.1.1)) (fun _ => 0) 0 := by
  rw [kernelProt_congr_m L γ δ _ H1 _ (fun K' => K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
      (IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
        (K.capInd layer hLayer dag K' : ℂ))) _ s' _ _ _ _ (fun κ => K.m1_eq layer hLayer hGeo L γ δ s h roots Rf dag κ)]
  exact kernelProt_const_mul L γ δ _ H1 _ _ _ s' _ _ _ _

end CapP

end WaveTurbulence.Flower.MkSlotsB
