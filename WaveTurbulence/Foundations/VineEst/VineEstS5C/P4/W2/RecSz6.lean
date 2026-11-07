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

/-! # P4-W2 (session 19, step 2): `Src.sz` of every summand of the step and bottom sources against the native row bounds

`hg_of_op`: the incoherency indices of the operative rows vanish.  `rows_N0_bot`: `rows_N0` at the bottom level.
`srcOfC_sz_rows`, `botSrcOfC_sz_rows`: `Src.sz c' ≤ KZ · (rowBoundH(pair row) · rowBoundH(branch row)) · Lw^{[recKind c' = 3]}`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13


variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem hg_of_op (hM9 : VineParamContract.VINEPARAM) (lv : Lvl B) (pstar : lv.ι) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = ((lv.state B RD hG layer hLayer).family.placement pstar).lower) :
    rowCoupleG hM9 B RD hG layer hLayer (assemblyPairBij hG B hM9 p0) = 0 ∧
      rowTreeG hM9 B RD hG layer hLayer (assemblyBranchBij hM9 B c0) = 0 := by
  have hcc := hop.some.coupleCoherent
  have htc := hop.some.treeCoherent
  constructor
  · refine rowCoupleG_eq_zero_of_cohOn hM9 B RD hG layer hLayer _ ?_
    rw [assemblyPairOf_bij]
    rw [hp0]
    exact hcc
  · refine rowTreeG_eq_zero_of_cohOn hM9 B RD hG layer hLayer _ ?_
    rw [assemblyBranchOf_bij]
    show CohOn _ ((RD.tree c0.1).linksAt _ _)
    rw [hc0]
    exact htc

theorem rows_N0_bot (hprime : IsPrimeGarden G) (hM9 : VineParamContract.VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {p : ℕ}
    (lv : Lvl B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (bb : BT w lv.ι)
    (hb : bb ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c) (B0 : ℝ)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = lv.c.b)
    (hg1 : rowCoupleG hM9 B RD hG layer hLayer (assemblyPairBij hG B hM9 p0) = 0)
    (hg2 : rowTreeG hM9 B RD hG layer hLayer (assemblyBranchBij hM9 B c0) = 0) :
    rowBoundH hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inl (assemblyPairBij hG B hM9 p0)) *
      rowBoundH hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inr (assemblyBranchBij hM9 B c0)) =
    rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN (lv.state B RD hG layer hLayer) pstar *
      (layerCost (fun _ => B0) (zpObjC bb.1 pstar) * layerCost (fun _ => B0) (zpObjT bb.1 pstar)) := by
  have hpp : p0.1 = pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).retained := hp0
  have hcc : c0.1 = ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).lower :=
    hc0.trans (Lvl.bottom_hb0 B RD hG layer hLayer lv pstar h0)
  have hup := hup_of_max B RD hG layer hLayer lv pstar h0 hmax
  rw [rowBoundH_inl_bij B RD hG layer hLayer hM9 W p0, rowBoundH_inr_bij B RD hG layer hLayer hM9 W c0, hg1, hg2,
    bot_leafCost_eq_native (lv.state B RD hG layer hLayer) lv.c hprime hop.some.canonical hop.some.eligible hop.some.treeCoherent
      hop.some.coupleCoherent hup B RD hG layer hLayer (lv.e pstar) (zpN_lvl B RD hG layer hLayer lv pstar) bb hb B0, ← hpp, ← hcc]
  have hs := native_size_start B RD hG layer hLayer (lv.e pstar)
  rw [← hpp, ← hcc] at hs
  have h1 := size_half_cpl (RD.couple p0.1)
  have h2 := size_half_chain (RD.tree c0.1)
  have hz : (RD.couple p0.1).size / 2 + (RD.tree c0.1).size / 2 = zpN (lv.state B RD hG layer hLayer) pstar := by
    rw [zpN_lvl]; omega
  unfold rowB
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
  rw [← hz, pow_add]
  ring

end WaveTurbulence.VineEstS5C.P4.W2
