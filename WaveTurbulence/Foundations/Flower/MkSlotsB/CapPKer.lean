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

end CapP

end WaveTurbulence.Flower.MkSlotsB
