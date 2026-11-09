/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Terms
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Bot.Terms
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family` (sha256 0c6106cdf9680f30…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # BOT-DECOMP: the bottom expansion family with `BotSurj`, `BotLayers`, `hq2` discharged (mirror of `P4.Family`)

At a level `lv` whose top operative member `pstar` has piece index `0`, the four operation preconditions (`canonical`, `eligible`, `treeCoherent`,
`coupleCoherent`) of `hop : lv.Op pstar` are exactly the hypotheses of `botSurj_of_state`, `botLayers_of_state` (the bottom mirror of ZP-SURJ's export) and of
ZP-SURJ's `zpQ2_le_of_state` (`P4.hq2_of_op`).  So `bundleBotFamOf hR SFF` is the bottom expansion family; its only inputs are PL234's `RealityAll`
and the separated expansions `SFF` of the approximants at the bottom vine (P2 gate data, as `P4.SepFamFam` at the other members).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4

set_option linter.unusedSectionVars false

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}

/-- At the top operative member of piece index `0`, every other member is inert (the situation of `4d-B2`'s `hup`). -/
theorem hup_of_maxΓ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :
    ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j) := by
  intro j hjp
  refine ⟨fun op => hjp ?_⟩
  have h1 := hmax j ⟨op⟩
  have h2 : (lv.e j).1.val = (lv.e pstar).1.val := by omega
  exact lv.he (Subtype.ext (Fin.ext h2))

theorem botSurj_of_opΓ (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :
    BotSurj p kind pstar (lv.state B RD hG layer hLayer) lv.c :=
  botSurj_of_state (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent
    hop.some.coupleCoherent lv.c hprime (hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax)

theorem botLayers_of_opΓ (hprime : IsPrimeGarden G) (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :
    BotLayers p kind pstar (lv.state B RD hG layer hLayer) lv.c :=
  botLayers_of_state (lv.state B RD hG layer hLayer) hop.some.canonical hop.some.eligible hop.some.treeCoherent
    hop.some.coupleCoherent lv.c hprime (hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax)

variable (p kind) in
/-- The separated expansions of the approximants at every bottom vine (from P2's gate data). -/
abbrev BotSepFamFamΓ (κ0 : KPar d) : Type 1 :=
  ∀ (lv : LvlΓ B) (pstar : lv.ι), (lv.e pstar).1.val = 0 → lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar →
    (∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) →
    BotSepFam p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0

open Classical in
/-- **`BotExp` of a bottom level** from the separated expansions `SF`, and `hR` (PL234 `reality_all`). -/
noncomputable def bundleBotExpOfΓ (hprime : IsPrimeGarden G) (hR : P1.RealityAll) (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (SF : BotSepFam p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0) :
    BotExpΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 lv pstar where
  Ch := Ch SF.S
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      botA p kind pstar (lv.state B RD hG layer hLayer) lv.c else botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
    (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
      botB p kind pstar (lv.state B RD hG layer hLayer) lv.c else botA p kind pstar (lv.state B RD hG layer hLayer) lv.c)
    (botA p kind pstar (lv.state B RD hG layer hLayer) lv.c) (botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
  term := fun c x t u => botTerm p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0 SF _ _ c x t u
  Win := BotWin p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0 SF
  eq := fun x t u hW => psiBot_eq_sum_terms hR (botSurj_of_opΓ B RD hG layer hLayer hprime lv pstar h0 hop hmax)
    (botLayers_of_opΓ B RD hG layer hLayer hprime lv pstar h0 hop hmax) κ0 SF _ _
    ⟨fun h => by simp [if_pos h], fun h => by simp [if_neg h]⟩ x t u hW

/-- The number of summands of a bottom level's bundle (`card_botCh`). -/
theorem card_bundleBotExpOfΓ (hprime : IsPrimeGarden G) (hR : P1.RealityAll) (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0)
    (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (SF : BotSepFam p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0) :
    Fintype.card (bundleBotExpOfΓ B RD hG layer hLayer hprime hR lv pstar h0 hop hmax SF).Ch =
      3 * ((∑ b ∈ botA p kind pstar (lv.state B RD hG layer hLayer) lv.c, SF.S.mQ b * SF.S.mT b) +
          ∑ b ∈ botB p kind pstar (lv.state B RD hG layer hLayer) lv.c, SF.S.mQ b * SF.S.mT b) +
        ((∑ b ∈ botA p kind pstar (lv.state B RD hG layer hLayer) lv.c, (SF.S.mQ b + SF.S.mT b + 1)) +
          ∑ b ∈ botB p kind pstar (lv.state B RD hG layer hLayer) lv.c, (SF.S.mQ b + SF.S.mT b + 1)) := by
  classical
  unfold bundleBotExpOfΓ
  show Fintype.card (Ch _ _ _ _ _) = _
  exact card_botCh κ0 SF

/-- **The bottom expansion family** (`bundleBotExpOf` at every bottom level). -/
noncomputable def bundleBotFamOfΓ (hprime : IsPrimeGarden G) (hR : P1.RealityAll) (SFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0) :
    BotExpFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 :=
  fun lv pstar h0 hop hmax => bundleBotExpOfΓ B RD hG layer hLayer hprime hR lv pstar h0 hop hmax (SFF lv pstar h0 hop hmax)

/-- The summand `c` of the bottom family is `botTerm` (the frame times `bFac` times `νA` times the piece/remainder summand). -/
theorem bundleBotFamOf_termΓ (hprime : IsPrimeGarden G) (hR : P1.RealityAll) (SFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)
    (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (bundleBotFamOfΓ B RD hG layer hLayer hprime hR SFF lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) :
    (bundleBotFamOfΓ B RD hG layer hLayer hprime hR SFF lv pstar h0 hop hmax).term c x t u =
      botTerm p kind pstar (lv.state B RD hG layer hLayer) lv.c κ0 (SFF lv pstar h0 hop hmax) _ _ c x t u := rfl

/-- **The windows of the bottom family hold under the exterior window** (`WinOfExtBot`). -/
theorem winOfExtBot_bundleBotFamOfΓ (hprime : IsPrimeGarden G) (hR : P1.RealityAll) (SFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0) :
    WinOfExtBotΓ B RD hG layer hLayer (bundleBotFamOfΓ B RD hG layer hLayer hprime hR SFF) := by
  intro lv pstar h0 hop hmax x u hu
  exact botWin_holds κ0 (SFF lv pstar h0 hop hmax) (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0) (retParent _)
    (hq2_of_opΓ B RD hG layer hLayer lv pstar hop) x u hu

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
