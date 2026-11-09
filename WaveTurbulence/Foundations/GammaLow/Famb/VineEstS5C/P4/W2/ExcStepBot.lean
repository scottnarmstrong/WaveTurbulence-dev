/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ExcStep
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot` (sha256 3946ec430deb1fb2…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 7, step 3l): the exceptional factor of a bottom record as a bundle summand

`botX_eq`: `botX .. c x u = ν · bundlePtG (CaseA A) (BSFF ..).S bs₁ bs₂ (botA) (botB) (botRemQ ..) (botRemT ..) (botVars κ0 A lv.c pstar x u) c` (by definition; the bottom data is `botVars`, with no restriction `rA`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w}
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime' : IsPrimeGarden G}
variable (hR : RealityAll) (BSFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

open Classical in
theorem botX_eqΓ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (c : (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR BSFF lv pstar h0 hop hmax).Ch) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) :
    botXΓ B RD hG layer hLayer hR hprime' BSFF lv pstar h0 hop hmax c x u =
      ((nuOf (lv.state B RD hG layer hLayer) pstar : ℤˣ) : ℂ) *
        bundlePtG (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) (BSFF lv pstar h0 hop hmax).S
          (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
            botA p kind pstar (lv.state B RD hG layer hLayer) lv.c else botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
          (if CaseA (pstar := pstar) (lv.state B RD hG layer hLayer) then
            botB p kind pstar (lv.state B RD hG layer hLayer) lv.c else botA p kind pstar (lv.state B RD hG layer hLayer) lv.c)
          (botA p kind pstar (lv.state B RD hG layer hLayer) lv.c) (botB p kind pstar (lv.state B RD hG layer hLayer) lv.c)
          (botRemQ pstar κ0 (botQfam pstar κ0 (lv.state B RD hG layer hLayer)))
          (botRemT pstar κ0 (botTfam pstar κ0 (lv.state B RD hG layer hLayer)))
          (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).1
          (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.1
          (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.1
          (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.1
          (botVars κ0 (lv.state B RD hG layer hLayer) lv.c pstar x u).2.2.2.2 c := by
  unfold botXΓ
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
