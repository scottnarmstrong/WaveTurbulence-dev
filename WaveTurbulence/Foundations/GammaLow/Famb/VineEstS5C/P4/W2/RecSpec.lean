/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBlock
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecKind
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecF0
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecClause
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSupp2
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecBlock
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecSupp2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec` (sha256 f0b3978469de1949…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 17, step 1): `RecKind`, `RepConcl`, `RecSpec`, `exists_recSpec`

`recKind c' = 3` for an outer-`inr` (remainder) summand, `kindOf c'` otherwise; `kd = 1 ↔ kindOf = 1`, `kd ≠ 2 ↔ kindOf ≠ 2`.
`RepConcl`: the conclusion of `rec_step01`/`rec_bot01` for a record `r` with the number `kd` in place of `kindOf c`.
`RecSpec`: for every engine parameter set whose `add` contains `addr`, a non-kind-2 record has `RepConcl` with bound `bnd`.
`exists_recSpec`: every record of `ExcOf` has a `RecSpec` (given the certified sources of the level members and `DispK01`; kind 2 is NOT covered here).
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
variable {κ0 : KPar P.d}

open VineParamContract in
/-- **The representation conclusion** of `rec_step01`/`rec_bot01` for the record `r`, with the number `kd` in place of `kindOf c`. -/
def RepConclΓ (hM9 : NormalChartSupply γF) (hL : κ0.L ≠ 0) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) (wN wDec : ℕ)
    (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (Bx : Set (Fin 3 → ℝ)) (kd : ℕ) (zc : Prop) (r : ExcRec G P.d) (hp : r.p0 ∈ clRegionalPairs hG U)
    (hbj : r.bj ∈ clInteriorBranches R) (bnd : ℝ≥0∞) : Prop :=
  ∃ (ε : ℝ) (Xr : ((assemblyShapeΓ hM9 B).TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ),
    |ε| = 1 ∧
    PieceRepU (P := P) (D := engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g')
      (assemblyShape_I_posΓ hM9 B) (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩) (assemblyBranchBijΓ hM9 B ⟨r.bj, hbj⟩) ε
      (f0Of P.η (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩).1 kd) Xr bnd Bx ∧
    (zc → ∀ tt ∈ Bx, ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
      τ ∈ (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g').timeDom
        (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) → ∀ (rr k : Mom P.d), Xr τ tt rr k = 0) ∧
    ∀ (β : Fin 4 → (Fin P.d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
      (x : (assemblyShapeΓ hM9 B).VIdx → (Fin P.d → ℤ)) (tt : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ),
      r.X (clExtendIndices R ((clNormalizedChainEquivΓ hL B κ0.base β hβ hM9).symm x).1)
          (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) =
        Xr τ tt (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1)
          (rowMom (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
            (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
            (Sum.inl (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩))) ∧
      rowMom (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
          (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
          (Sum.inr (assemblyBranchBijΓ hM9 B ⟨r.bj, hbj⟩)) =
        rowMom (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g') κ0.L x
          (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)))
          (Sum.inl (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩)) +
        ε • (sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => κ0.base + latticePoint κ0.L (β j)) 1)

open VineParamContract in
/-- **The specification of a record**: `kd ≤ 3`; whenever the engine parameters have the order atoms `addr` in `add`, a non-kind-2 record has
the representation conclusion with the bound `bnd`. -/
def RecSpecΓ (hM9 : NormalChartSupply γF) (hL : κ0.L ≠ 0) (r : ExcRec G P.d) (hp : r.p0 ∈ clRegionalPairs hG U)
    (hbj : r.bj ∈ clInteriorBranches R) (kd : ℕ) (zc : Prop) (addr : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (bnd : ℝ≥0∞) : Prop :=
  kd ≤ 3 ∧ (kd = 2 → 0 < (assemblyShapeΓ hM9 B).m (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩).1) ∧
    RecClause0Γ B hM9 (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩).1 kd zc addr ∧ SuppConclΓ B hM9 r.X r.bj zc addr ∧ ∀ (W : SumintWeightClockData (assemblyShapeΓ hM9 B) P.d) (wN wDec : ℕ) (_ : wN + 1 = 30 * P.d) (_ : wDec = 30 * P.d)
    (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4) (Bex : Finset (GBranch G.tree))
    (add : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (_ : W.q = assemblyTimeQΓ hM9 B (layC RD hG layer)) (Bx : Set (Fin 3 → ℝ))
    (_ : Bx ⊆ outBox (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g'))
    (_ : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1),
    (¬ zc → addr ⊆ add) → RepConclΓ B RD hG layer hM9 hL W wN wDec bk Bex add g g' Bx kd zc r hp hbj bnd

open VineParamContract in
theorem SuppConclΓ.mono_zc {hM9 : NormalChartSupply γF} {d : ℕ} {X : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ} {bj : GBranch G.tree}
    {zc zc' : Prop} {addr : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)}
    (h : SuppConclΓ B hM9 X bj zc addr) (hz : zc → zc') : SuppConclΓ B hM9 X bj zc' addr :=
  fun x u hx => ⟨fun hn => (h x u hx).1 (fun h' => hn (hz h')), (h x u hx).2⟩

open VineParamContract in
theorem RecClause0Γ.mono_zc {hM9 : NormalChartSupply γF} {i : Fin (assemblyShapeΓ hM9 B).I} {kd : ℕ} {zc zc' : Prop}
    {addr : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)}
    (h : RecClause0Γ B hM9 i kd zc addr) (hz : zc → zc') : RecClause0Γ B hM9 i kd zc' addr :=
  fun hk hn => h hk (fun h' => hn (hz h'))

open VineParamContract in
/-- **The slots of a record at a type-II vine** (`qb ≠ qr`): `σ₁`, `σ₂` are the two clock atoms of the block, distinct, and the kind-2 factor is their rigid factor. -/
theorem rec_htsΓ (η : ℝ) (hM9 : NormalChartSupply γF) (lv : LvlΓ B) (pstar : lv.ι) (lo : GBranch G.tree)
    (hlo : lo = (assemblyPieceAtΓ B (lv.e pstar).1).lower) (ν : ℤˣ)
    (hne : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) ≠
      qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) :
    ∃ (sa ta : (assemblyShapeΓ hM9 B).TVar),
      (recSlotsΓ hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 1 = Sum.inl sa ∧
        recSlotsΓ hM9 B lo (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
          (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) ν 2 = Sum.inl ta) ∧
      sa ≠ ta ∧ ∀ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
        k2f (S := assemblyShapeΓ hM9 B) η (lv.e pstar).1 τ = ((|τ sa - τ ta| ^ (1 - 3 * η) : ℝ) : ℂ) := by
  subst hlo
  obtain ⟨hm, -, h1⟩ := rec_slots_typeIIΓ B RD hG layer hLayer hM9 lv pstar ν hne
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨.inr (.inl ⟨(lv.e pstar).1, ⟨0, hm⟩⟩), .inl ⟨(lv.e pstar).1, ⟨1, by omega⟩⟩, ⟨e1, e2⟩, by simp, fun τ => ?_⟩
    unfold k2f
    rw [dif_pos hm, abs_sub_comm]
  · refine ⟨.inl ⟨(lv.e pstar).1, ⟨1, by omega⟩⟩, .inr (.inl ⟨(lv.e pstar).1, ⟨0, hm⟩⟩), ⟨e1, e2⟩, by simp, fun τ => ?_⟩
    unfold k2f
    rw [dif_pos hm]

section Exists
variable {hprime : IsPrimeGarden G} (hR : RealityAll) (SFF : SepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)
  (hprime' : IsPrimeGarden G) (BSFF : BotSepFamFamΓ (p := p) (kind := kind) B RD hG layer hLayer κ0)

/-- The certified source of the step bundle at an operative member. -/
abbrev StepSrcΓ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar) :=
  Src P (SFF lv pstar hk hop).S (remQ κ0 (zpQfam κ0 (lv.state B RD hG layer hLayer)))
    (remT κ0 (zpTfam κ0 (lv.state B RD hG layer hLayer))) ((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)
    ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)

/-- The goodness hypothesis of `rec_step01`. -/
def StepGoodΓ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (src : StepSrcΓ B RD hG layer hLayer SFF lv pstar hk hop) : Prop :=
  ∀ b', (b' ∈ bsA p kind {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
        (lv.split B RD hG layer hLayer pstar hk) hprime ∨ b' ∈ bsB p kind {j | (lv.e j).1.val < (lv.e pstar).1.val}
        (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime) → src.good b'

/-- The certified source of the bottom bundle. -/
abbrev BotSrcΓ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val) :=
  Src P (BSFF lv pstar h0 hop hmax).S
      (botRemQ pstar κ0 (botQfam pstar κ0 (lv.state B RD hG layer hLayer)))
      (botRemT pstar κ0 (botTfam pstar κ0 (lv.state B RD hG layer hLayer)))
      ((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ)

/-- The goodness hypothesis of `rec_bot01`. -/
def BotGoodΓ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
    (src : BotSrcΓ B RD hG layer hLayer BSFF lv pstar h0 hop hmax) : Prop :=
  ∀ b', (b' ∈ botA p kind pstar (lv.state B RD hG layer hLayer) lv.c ∨ b' ∈ botB p kind pstar (lv.state B RD hG layer hLayer) lv.c) → src.good b'

open VineParamContract in
/-- **Every record of `ExcOf` has a `RecSpec`** (kind 2 is excluded inside `RecSpec`; the sources of the level members and `DispK01` are inputs). -/
theorem exists_recSpecΓ {K0 : ℝ≥0∞} {Rb : ℝ} (hdisp : DispK01.{0} P K0) (hd2 : DispK2.{0} P Rb K0) (hM9 : NormalChartSupply γF) (hL : κ0.L ≠ 0)
    (srcS : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      StepSrcΓ B RD hG layer hLayer SFF lv pstar hk hop)
    (hgS : ∀ lv pstar hk hop, StepGoodΓ B RD hG layer hLayer SFF lv pstar hk hop (srcS lv pstar hk hop))
    (srcB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      BotSrcΓ B RD hG layer hLayer BSFF lv pstar h0 hop hmax)
    (hgB : ∀ lv pstar h0 hop hmax, BotGoodΓ B RD hG layer hLayer BSFF lv pstar h0 hop hmax (srcB lv pstar h0 hop hmax))
    (Kz Lw : ℝ) (ZB : ↥(clRegionalPairs hG U) → ↥(clInteriorBranches R) → ℝ)
    (hszS : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (c' : (bundleExpOfΓ B RD hG layer hLayer hR lv pstar hk (zpSurj_of_opΓ B RD hG layer hLayer lv pstar hk hop)
        (zpLayers_of_opΓ B RD hG layer hLayer lv pstar hk hop) (retParent _) (SFF lv pstar hk hop)).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = (lv.split B RD hG layer hLayer pstar hk).sb.b),
      (srcS lv pstar hk hop).sz c' ≤ Kz * ZB p0 c0 * (if recKind c' = 3 then Lw else 1))
    (hszB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val)
      (c : (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR BSFF lv pstar h0 hop hmax).Ch)
      (p0 : ↥(clRegionalPairs hG U)) (_ : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
        ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
      (c0 : ↥(clInteriorBranches R)) (_ : c0.1 = lv.c.b),
      (srcB lv pstar h0 hop hmax).sz c ≤ Kz * ZB p0 c0 * (if recKind c = 3 then Lw else 1))
    (xsS : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross P (srcS lv pstar hk hop))
    (xsB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      ((zpQ4 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1 ≤ ((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) →
        K2.XCross P (srcB lv pstar h0 hop hmax))
    (Kx0 : ℝ) (hKx1 : 1 ≤ Kx0)
    (hKxS : ∀ lv pstar hk hop h, (xsS lv pstar hk hop h).Kx ≤ Kx0)
    (hKxB : ∀ lv pstar h0 hop hmax h, (xsB lv pstar h0 hop hmax h).Kx ≤ Kx0)
    (hRbS : ∀ (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ Rb)
    (hRbB : ∀ (lv : LvlΓ B) (pstar : lv.ι) (h0 : (lv.e pstar).1.val = 0) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
      (hmax : ∀ j, lv.Op (p := p) (kind := kind) B RD hG layer hLayer j → (lv.e j).1.val ≤ (lv.e pstar).1.val),
      max (((zpQh (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) (((zpQ2 (lv.state B RD hG layer hLayer) pstar : ℕ) : ℝ) + 1) ≤ Rb)
    (r : ExcRec G P.d)
    (hr : ExcOfΓ B RD hG layer hLayer (bundleFamOfΓ B RD hG layer hLayer hR SFF) (bundleBotFamOfΓ B RD hG layer hLayer hprime' hR BSFF)
      (stepXΓ B RD hG layer hLayer hR SFF) (botXΓ B RD hG layer hLayer hR hprime' BSFF) U r)
    (hp : r.p0 ∈ clRegionalPairs hG U) (hbj : r.bj ∈ clInteriorBranches R) :
    ∃ (kd : ℕ) (zc : Prop) (addr : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (bnd : ℝ≥0∞),
      RecSpecΓ B RD hG layer hM9 hL r hp hbj kd zc addr bnd ∧
      bnd ≤ Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal (Kz * ZB ⟨r.p0, hp⟩ ⟨r.bj, hbj⟩ * (if kd = 3 then Lw else 1)) := by
  classical
  have hblk' := excOf_pairBij_fstΓ B RD hG layer hLayer _ _ _ _ hM9 hr hp
  rcases hr with ⟨lv, pstar, hk, hop, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩ | ⟨lv, pstar, h0, hop, hmax, c, f, hreal, hf, hp0, hbj', hblk, hrX⟩
  · set c' := castChΓ B RD hG layer hLayer hR SFF lv pstar hk hop c with hc'
    set σ := recSlotsΓ hM9 B (lv.split B RD hG layer hLayer pstar hk).sb.b
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
        (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
        (nuOf (lv.state B RD hG layer hLayer) pstar) with hσ
    have hi : (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩).1 = (lv.e pstar).1 := Fin.ext (hblk'.trans hblk)
    have hzold : (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c') σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ recKind c' = 0)) →
        (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c') σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c' = 0 ∨ recKind c' = 2))) :=
      fun h => h.elim Or.inl (fun h => Or.inr ⟨h.1, Or.inl h.2⟩)
    have key : ∀ (u v : GBranch G.tree) (ν : ℤˣ), u = v →
        brSlotΓ hM9 B (if ν = 1 then v else u) = brSlotΓ hM9 B (if ν = 1 then u else v) := by
      intro u v ν h; subst h; simp
    have h12 : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) → σ 1 = σ 2 :=
      fun hqq => by simp only [hσ, recSlotsΓ]; simp; exact key _ _ _ hqq
    obtain ⟨kd', hkd3, hkd0, hkdr⟩ := exists_kd' (recKind c') (recKind_le_three c')
      (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
    have hzk : (recKind c' = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) →
        (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c') σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c' = 0 ∨ recKind c' = 2))) :=
      fun h => Or.inr ⟨h.2, Or.inr h.1⟩
    refine ⟨kd', (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c') σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c' = 0 ∨ recKind c' = 2))),
      ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c') σ,
      Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal ((srcS lv pstar hk hop).sz c'), ⟨hkd3, ?_, ?_, ?_, ?_⟩,
      ?_⟩
    · intro hk2
      rw [hi]
      by_cases h2 : recKind c' = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
      · rw [hkd0 h2] at hk2; omega
      · rw [hkdr h2] at hk2
        obtain ⟨hm, -⟩ := rec_slots_typeIIΓ B RD hG layer hLayer hM9 lv pstar (nuOf (lv.state B RD hG layer hLayer) pstar)
          (fun h => h2 ⟨hk2, h⟩)
        exact hm
    · rw [hi]
      intro hk0 hn
      by_cases h2 : recKind c' = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
      · exact absurd (hzk h2) hn
      · rw [hkdr h2] at hk0
        exact (RecClause0Γ.mono_zc B (rec_clause0Γ B RD hG layer hLayer hM9 lv pstar _ (split_sb_bΓ B RD hG layer hLayer lv pstar hk) c' _) hzold) hk0 hn
    · rw [hbj']
      exact SuppConclΓ.mono_zc B (supp_stepΓ B RD hG layer hLayer hR SFF hM9 lv pstar hk hop c hreal r.X f hf hrX) hzold
    swap
    · have hb := hszS lv pstar hk hop c' ⟨r.p0, hp⟩ hp0 ⟨r.bj, hbj⟩ hbj'
      have hk3 : (kd' = 3) ↔ (recKind c' = 3) := by
        by_cases h2 : recKind c' = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
            qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
        · rw [hkd0 h2]; omega
        · rw [hkdr h2]
      simp only [hk3]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb)
    intro W wN wDec hwN hwDec bk Bex add g g' hq Bx hBx hext hadd
    obtain ⟨ε, Xr, h1, h2, hz, h3⟩ := rec_step01Γ B RD hG layer hLayer hR SFF hdisp hd2 hM9 W wN wDec hwN hwDec bk Bex add g g' hq lv pstar hk hop c
      hreal (srcS lv pstar hk hop) (xsS lv pstar hk hop) Kx0 hKx1 (hKxS lv pstar hk hop) (hRbS lv pstar hk hop) (hgS lv pstar hk hop)
      r.p0 hp hp0 r.bj hbj hbj' r.X f hf hrX hL lv.hcb Bx hBx hext _ (fun h => Or.inl h)
      (fun hqq hk2 => Or.inr ⟨hqq, Or.inr ((recKind_eq_two_iff' c').2 hk2)⟩)
      (fun hne => rec_htsΓ B RD hG layer hLayer P.η hM9 lv pstar _ (split_sb_bΓ B RD hG layer hLayer lv pstar hk) _ hne)
      hadd
      (fun hz τ tt htop x y => bundle_zero_of_zc _ c' σ (recSlots_wfΓ hM9 B _ _ _ _) _ h12 _ _ hz τ tt htop x y)
    refine ⟨ε, Xr, h1, ?_, hz, h3⟩
    rw [← hc'] at h2
    by_cases h2' : recKind c' = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
    · rw [hkd0 h2']
      refine pieceRepU_zero (assemblyShape_I_posΓ hM9 B) _ _ _ _ _ _ _ (fun tt htt => ?_)
      filter_upwards [hz (hzk h2') tt htt] with τ hτ hmem r k hr
      exact hτ hmem r k
    · have hf := f0Of_recKind (S := (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g').S) (d := P.d) P.η (lv.e pstar).1 c'
      rw [hkdr h2', hi, hf]
      exact h2
  · set σ := recSlotsΓ hM9 B lv.c.b
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar))
        (qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
        (nuOf (lv.state B RD hG layer hLayer) pstar) with hσ
    have hi : (assemblyPairBijΓ hG B hM9 ⟨r.p0, hp⟩).1 = (lv.e pstar).1 := Fin.ext (hblk'.trans (hblk.trans h0.symm))
    have hlowc : lv.c.b = (assemblyPieceAtΓ B (lv.e pstar).1).lower :=
      (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0).trans (start_lowerΓ B RD hG layer hLayer (lv.e pstar))
    have hzold : (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c) σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ recKind c = 0)) →
        (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c) σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
          qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c = 0 ∨ recKind c = 2))) :=
      fun h => h.elim Or.inl (fun h => Or.inr ⟨h.1, Or.inl h.2⟩)
    have key : ∀ (u v : GBranch G.tree) (ν : ℤˣ), u = v →
        brSlotΓ hM9 B (if ν = 1 then v else u) = brSlotΓ hM9 B (if ν = 1 then u else v) := by
      intro u v ν h; subst h; simp
    have h12 : qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) =
        qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) → σ 1 = σ 2 :=
      fun hqq => by simp only [hσ, recSlotsΓ]; simp; exact key _ _ _ hqq
    obtain ⟨kd', hkd3, hkd0, hkdr⟩ := exists_kd' (recKind c) (recKind_le_three c)
      (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar))
    have hzk : (recKind c = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)) →
        (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c) σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c = 0 ∨ recKind c = 2))) :=
      fun h => Or.inr ⟨h.2, Or.inr h.1⟩
    refine ⟨kd', (ordBad (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c) σ ∨
        (qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar) ∧ (recKind c = 0 ∨ recKind c = 2))),
      ordPairs (ordRels (CaseA (pstar := pstar) (lv.state B RD hG layer hLayer)) c) σ,
      Kall P.d (K0 * ENNReal.ofReal Kx0) * ENNReal.ofReal ((srcB lv pstar h0 hop hmax).sz c), ⟨hkd3, ?_, ?_, ?_, ?_⟩,
      ?_⟩
    · intro hk2
      rw [hi]
      by_cases h2 : recKind c = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
      · rw [hkd0 h2] at hk2; omega
      · rw [hkdr h2] at hk2
        obtain ⟨hm, -⟩ := rec_slots_typeIIΓ B RD hG layer hLayer hM9 lv pstar (nuOf (lv.state B RD hG layer hLayer) pstar)
          (fun h => h2 ⟨hk2, h⟩)
        exact hm
    · rw [hi]
      intro hk0 hn
      by_cases h2 : recKind c = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
      · exact absurd (hzk h2) hn
      · rw [hkdr h2] at hk0
        exact (RecClause0Γ.mono_zc B (rec_clause0Γ B RD hG layer hLayer hM9 lv pstar _ hlowc c _) hzold) hk0 hn
    · rw [hbj']
      exact SuppConclΓ.mono_zc B (supp_botΓ B RD hG layer hLayer hR BSFF hM9 lv pstar h0 hop hmax c hreal r.X f hrX) hzold
    swap
    · have hb := hszB lv pstar h0 hop hmax c ⟨r.p0, hp⟩ hp0 ⟨r.bj, hbj⟩ hbj'
      have hk3 : (kd' = 3) ↔ (recKind c = 3) := by
        by_cases h2 : recKind c = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
        · rw [hkd0 h2]; omega
        · rw [hkdr h2]
      simp only [hk3]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb)
    intro W wN wDec hwN hwDec bk Bex add g g' hq Bx hBx hext hadd
    obtain ⟨ε, Xr, h1, h2, hz, h3⟩ := rec_bot01Γ B RD hG layer hLayer hR BSFF hdisp hd2 hM9 W wN wDec hwN hwDec bk Bex add g g' hq lv pstar h0 hop hmax c
      hreal (srcB lv pstar h0 hop hmax) (xsB lv pstar h0 hop hmax) Kx0 hKx1 (hKxB lv pstar h0 hop hmax) (hRbB lv pstar h0 hop hmax)
      (hgB lv pstar h0 hop hmax) r.p0 hp hp0 r.bj hbj hbj' r.X f hf hrX hL lv.hcb Bx hBx hext _ (fun h => Or.inl h)
      (fun hqq hk2 => Or.inr ⟨hqq, Or.inr ((recKind_eq_two_iff' c).2 hk2)⟩)
      (fun hne => rec_htsΓ B RD hG layer hLayer P.η hM9 lv pstar _ hlowc _ hne)
      hadd
      (fun hz τ tt htop x y => bundle_zero_of_zc _ c σ (recSlots_wfΓ hM9 B _ _ _ _) _ h12 _ _ hz τ tt htop x y)
    refine ⟨ε, Xr, h1, ?_, hz, h3⟩
    by_cases h2' : recKind c = 2 ∧ qbOf ((lv.state B RD hG layer hLayer).family.placement pstar) = qrOf ((lv.state B RD hG layer hLayer).family.placement pstar)
    · rw [hkd0 h2']
      refine pieceRepU_zero (assemblyShape_I_posΓ hM9 B) _ _ _ _ _ _ _ (fun tt htt => ?_)
      filter_upwards [hz (hzk h2') tt htt] with τ hτ hmem r k hr
      exact hτ hmem r k
    · have hf := f0Of_recKind (S := (engDatumΓ hM9 B hG W wN wDec bk (consXΓ hM9 B (layC RD hG layer) Bex add) g g').S) (d := P.d) P.η (lv.e pstar).1 c
      rw [hkdr h2', hi, hf]
      exact h2

end Exists

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
