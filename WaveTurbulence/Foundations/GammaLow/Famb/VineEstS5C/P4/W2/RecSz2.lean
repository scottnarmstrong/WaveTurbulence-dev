/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNum1
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.TermNum1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz2` (sha256 093a9a618c921ee8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 18, step 4c-2): native row bounds at a pair row and a branch row

`rowBoundH_inl_bij`, `rowBoundH_inr_bij`: `rowBoundH` at `assemblyPairBij p0` / `assemblyBranchBij c0` is `rowB (size/2) g · layerCost`.  `sz_le_rows`: the algebra
`4 TR² C₁⁴ (C₁² δ)^N (cost_C cost_T) ≤ (4 TR²/cb²) · rowB nC' 0 cost_C' · rowB nT' 0 cost_T'` for `nC' + nT' = N`, `cost_C cost_T = cost_C' cost_T'`.
-/

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
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

variable {Bh : ℕ → ℝ}

theorem rowBoundH_inl_bijΓ (hM9 : NormalChartSupply γF) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (p0 : ↥(clRegionalPairs hG U)) :
    rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inl (assemblyPairBijΓ hG B hM9 p0)) =
      rowB P ((RD.couple p0.1).size / 2) (rowCoupleGΓ hM9 B RD hG layer hLayer (assemblyPairBijΓ hG B hM9 p0)) *
        layerCost Bh (nativeCoupleLayered RD hG layer hLayer p0.1) := by
  simp only [rowBoundHΓ, rowBoundΓ, rowCostHΓ, rowCoupleΓ, rowCoupleLGΓ, assemblyPairOf_bijΓ hM9 B hG p0]

theorem rowBoundH_inr_bijΓ (hM9 : NormalChartSupply γF) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (c0 : ↥(clInteriorBranches R)) :
    rowBoundHΓ hM9 B RD hG layer hLayer P Bh W (Sum.inr (assemblyBranchBijΓ hM9 B c0)) =
      rowB P ((RD.tree c0.1).size / 2) (rowTreeGΓ hM9 B RD hG layer hLayer (assemblyBranchBijΓ hM9 B c0)) *
        layerCost Bh (nativeChainLayered RD hG layer hLayer c0.1) := by
  simp only [rowBoundHΓ, rowBoundΓ, rowCostHΓ, rowTreeΓ, rowTreeLGΓ, assemblyBranchOf_bijΓ hM9 B c0]
