/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz6
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz7
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.Final.BotCount
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSz6
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz7` (sha256 c3847ac2771a88d0…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 19, step 2): `stepSrcC`, `botSrcC` and their `Src.sz` bounds against the native row bounds -/

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
variable {κ : KPar P.d} {B0 : ℝ}

/-- **The certified source of a step level (chosen constants)**, at the operative member `pstar`. -/
noncomputable abbrev stepSrcCΓ (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)
    (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :=
  srcOfC (κ := κ) (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent Re E
    (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0

/-- **The certified source of the bottom level (chosen constants)**. -/
noncomputable abbrev botSrcCΓ (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)
    (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :=
  botSrcOfC (κ := κ) (lv.state B RD hG layer hLayer) lv.c hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    (hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax) Re E (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0

/-- **The cross fields of the step source.** -/
noncomputable def stepXCΓ (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0) (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4)
    (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (h : ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)) :
    K2.XCross P (stepSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar hk hop) :=
  srcOfCX (κ := κ) (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent Re E
    (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0 hη0 hη4 (by exact_mod_cast h)

/-- **The cross fields of the bottom source.** -/
noncomputable def botXCΓ (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0) (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4)
    (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (h : ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)) :
    K2.XCross P (botSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar h0 hop hmax) :=
  botSrcOfCX (κ := κ) (lv.state B RD hG layer hLayer) lv.c hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    (hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax) Re E (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0 hη0 hη4
    (by exact_mod_cast h)

open Classical in
theorem stepSrcC_sz_rowsΓ (hM9 : NormalChartSupply γF) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)
    (hη0 : 0 < P.η) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    {bs₁ bs₂ rA rB : Finset (ST w lv.ι pstar {j | (lv.e j).1.val < (lv.e pstar).1.val})}
    (c' : Ch (sffOfΓ (hprime := hprime) B RD hG layer hLayer E hord lv pstar hk hop).S bs₁ bs₂ rA rB)
    (hgood : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂ ∨ b ∈ rA ∨ b ∈ rB) →
      (stepSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar hk hop).good b)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = (lv.split B RD hG layer hLayer pstar hk).sb.b) :
    (stepSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar hk hop).sz c' ≤
      (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) *
        (rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inl (assemblyPairBijΓ hG B hM9 p0)) *
          rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inr (assemblyBranchBijΓ hM9 B c0))) *
        (if recKind c' = 3 then P.L ^ (-(P.gamma1 - Real.sqrt P.η)) else 1) := by
  have hcc : c0.1 = ((lv.state B RD hG layer hLayer).family.placement pstar).lower :=
    hc0.trans ((split_sb_bΓ B RD hG layer hLayer lv pstar hk).trans (start_lowerΓ B RD hG layer hLayer (lv.e pstar)).symm)
  obtain ⟨hg1, hg2⟩ := hg_of_opΓ B RD hG layer hLayer hM9 lv pstar hop p0 hp0 c0 hcc
  refine sz_le_kind (stepSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar hk hop) _ _ _ hgood ?_ c'
  exact srcOfC_idx (κ := κ) (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent Re E
    (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0 hη0 hη hcb hw _
    (fun bb hb => (rows_N0Γ B RD hG layer hLayer hM9 W lv pstar hk hop bb (mem_zpFinset_of_bs _ _ _ hb) B0 p0 hp0 c0 hc0 hg1 hg2).symm)

open Classical in
theorem botSrcC_sz_rowsΓ (hM9 : NormalChartSupply γF) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d)
    (hprime : IsPrimeGarden G) (Re : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)
    (hη0 : 0 < P.η) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    {bs₁ bs₂ rA rB : Finset (BT w lv.ι)}
    (c' : Ch (WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Final.botSffOfΓ (hprime := hprime) B RD hG layer hLayer E hord lv pstar h0 hop hmax).S bs₁ bs₂ rA rB)
    (hgood : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂ ∨ b ∈ rA ∨ b ∈ rB) →
      (botSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar h0 hop hmax).good b)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = lv.c.b) :
    (botSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar h0 hop hmax).sz c' ≤
      (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) *
        (rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inl (assemblyPairBijΓ hG B hM9 p0)) *
          rowBoundHΓ hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inr (assemblyBranchBijΓ hM9 B c0))) *
        (if recKind c' = 3 then P.L ^ (-(P.gamma1 - Real.sqrt P.η)) else 1) := by
  have hcc : c0.1 = ((lv.state B RD hG layer hLayer).family.placement pstar).lower :=
    hc0.trans (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0)
  obtain ⟨hg1, hg2⟩ := hg_of_opΓ B RD hG layer hLayer hM9 lv pstar hop p0 hp0 c0 hcc
  refine sz_le_kind (botSrcCΓ B RD hG layer hLayer hprime Re E hord hC1 hB0 lv pstar h0 hop hmax) _ _ _ hgood ?_ c'
  exact botSrcOfC_idx (κ := κ) (lv.state B RD hG layer hLayer) lv.c hprime
    hop.some.canonical hop.some.eligible hop.some.treeCoherent hop.some.coupleCoherent
    (hup_of_maxΓ B RD hG layer hLayer lv pstar h0 hmax) Re E (zpN_lvl_leΓ B RD hG layer hLayer hord lv pstar) hC1 hB0 hη0 hη hcb hw _
    (fun bb hb => (rows_N0_botΓ B RD hG layer hLayer hprime hM9 W lv pstar h0 hop hmax bb (mem_canon_of_botbs _ _ hb) B0 p0 hp0 c0 hc0 hg1 hg2).symm)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
