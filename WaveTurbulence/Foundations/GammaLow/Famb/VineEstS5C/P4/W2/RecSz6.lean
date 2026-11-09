/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotSz2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz5
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCoh
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz6
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecBotSz1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz6` (sha256 87f291200696fcf8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 19, step 2): `Src.sz` of every summand of the step and bottom sources against the native row bounds

`hg_of_op`: the incoherency indices of the operative rows vanish.  `rows_N0_bot`: `rows_N0` at the bottom level.
`srcOfC_sz_rows`, `botSrcOfC_sz_rows`: `Src.sz c' ≤ KZ · (rowBoundH(pair row) · rowBoundH(branch row)) · Lw^{[recKind c' = 3]}`.
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

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem hg_of_opΓ (hM9 : NormalChartSupply γF) (lv : LvlΓ B) (pstar : lv.ι) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = ((lv.state B RD hG layer hLayer).family.placement pstar).lower) :
    rowCoupleGΓ hM9 B RD hG layer hLayer (assemblyPairBijΓ hG B hM9 p0) = 0 ∧
      rowTreeGΓ hM9 B RD hG layer hLayer (assemblyBranchBijΓ hM9 B c0) = 0 := by
  have hcc := hop.some.coupleCoherent
  have htc := hop.some.treeCoherent
  constructor
  · refine rowCoupleG_eq_zero_of_cohOnΓ hM9 B RD hG layer hLayer _ ?_
    rw [assemblyPairOf_bijΓ]
    rw [hp0]
    exact hcc
  · refine rowTreeG_eq_zero_of_cohOnΓ hM9 B RD hG layer hLayer _ ?_
    rw [assemblyBranchOf_bijΓ]
    show CohOn _ ((RD.tree c0.1).linksAt _ _)
    rw [hc0]
    exact htc

theorem rows_N0_botΓ (hprime : IsPrimeGarden G) (hM9 : NormalChartSupply γF) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) {p : ℕ}
    (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (bb : BT w lv.ι)
    (hb : bb ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c) (B0 : ℝ)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = lv.c.b)
    (hg1 : rowCoupleGΓ hM9 B RD hG layer hLayer (assemblyPairBijΓ hG B hM9 p0) = 0)
    (hg2 : rowTreeGΓ hM9 B RD hG layer hLayer (assemblyBranchBijΓ hM9 B c0) = 0) :
    rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inl (assemblyPairBijΓ hG B hM9 p0)) *
      rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inr (assemblyBranchBijΓ hM9 B c0)) =
    rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN (lv.state B RD hG layer hLayer) pstar *
      (layerCost (fun _ => B0) (zpObjC bb.1 pstar) * layerCost (fun _ => B0) (zpObjT bb.1 pstar)) := by
  have hpp : p0.1 = pairOfLeaf G hG ((startStateΓ B RD hG layer hLayer).family.placement (lv.e pstar)).retained := hp0
  have hcc : c0.1 = ((startStateΓ B RD hG layer hLayer).family.placement (lv.e pstar)).lower :=
    hc0.trans (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0)
  have hup := hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax
  rw [rowBoundH_inl_bijΓ B RD hG layer hLayer hM9 W p0, rowBoundH_inr_bijΓ B RD hG layer hLayer hM9 W c0, hg1, hg2,
    bot_leafCost_eq_nativeΓ (lv.state B RD hG layer hLayer) lv.c hprime hop.some.canonical hop.some.eligible hop.some.treeCoherent
      hop.some.coupleCoherent hup B RD hG layer hLayer (lv.e pstar) (zpN_lvlΓ B RD hG layer hLayer lv pstar) bb hb B0, ← hpp, ← hcc]
  have hs := native_size_startΓ B RD hG layer hLayer (lv.e pstar)
  rw [← hpp, ← hcc] at hs
  have h1 := size_half_cpl (RD.couple p0.1)
  have h2 := size_half_chain (RD.tree c0.1)
  have hz : (RD.couple p0.1).size / 2 + (RD.tree c0.1).size / 2 = zpN (lv.state B RD hG layer hLayer) pstar := by
    rw [zpN_lvlΓ]; omega
  unfold rowB
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
  rw [← hz, pow_add]
  ring

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
