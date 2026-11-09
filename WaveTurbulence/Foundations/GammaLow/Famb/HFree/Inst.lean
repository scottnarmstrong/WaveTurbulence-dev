/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.HFree.Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcFam
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.HFree.Inst
public import WaveTurbulence.Foundations.GammaLow.Famb.HFree.Main
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ExcFam
-- L5b port of `WaveTurbulence.Foundations.VineEst.HFree.Inst` (sha256 a11a32d501ab48b5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # W2-HFREE (6): `hfreeAt_holds` at the actual families

`hfreeAt_holds_fam`: `HFreeAt` instantiated at `BE := bundleFamOf ..`, `BX := bundleBotFamOf ..`, `XE := stepX ..`, `XB := botX ..`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (hR : RealityAll) (SFF : SepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
variable (hprime' : IsPrimeGarden G) (BSFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

theorem hfreeAt_holds_famΓ (hM9 : NormalChartSupply γF) (hL : κ0.L ≠ 0)
    (hcan : CanonicalObject p kind (layeredReconstruction RD hG layer hLayer)) :
    HFreeAtΓ B RD hG layer hLayer (bundleFamOfΓ B RD hG layer hLayer hR SFF) (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR BSFF)
      (stepXΓ B RD hG layer hLayer hR SFF) (botXΓ B RD hG layer hLayer hR hprime' BSFF) hM9 :=
  hfreeAt_holdsΓ B RD hG layer hLayer _ _ _ _ hM9 hL (frameShapeX_bundleFamOfΓ B RD hG layer hLayer hR SFF)
    (botFrameShapeX_bundleBotFamOfΓ B RD hG layer hLayer hR hprime' BSFF) hcan

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
