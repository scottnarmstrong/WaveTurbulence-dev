/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz2
public import Mathlib
public import WaveTurbulence.Foundations.VineEst.HFree.Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.AuxLeaf3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSz2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz3` (sha256 c89eed5d8eb787ad…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 18, step 4c-3): the size algebra

`sz_idx_alg`: the four size products `szQ szT`, `szQ CRt`, `CRq szT`, `CRq CRt` of a good bundle member are bounded by `KZ · N` resp. `KZ · L^{-w} · N`, `N` the native row-bound product,
`KZ = 4 TR² trC²/cb²`.  `native_size_start`: the sizes of the native couple and tree of the start-state member add to `2 zpN`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.W13 TTree Finset WaveTurbulence.GammaLow.Famb.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem native_size_startΓ (i : (assemblySourceFamilyΓ B).CoreIndex) :
    (RD.couple (pairOfLeaf G hG ((startStateΓ B RD hG layer hLayer).family.placement i).retained)).size +
      (RD.tree ((startStateΓ B RD hG layer hLayer).family.placement i).lower).size =
      2 * zpN (startStateΓ B RD hG layer hLayer) i :=
  (Nat.add_comm _ _).trans (ZpSurj.two_zpN (startStateΓ B RD hG layer hLayer) (pstar := i)).symm

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
