/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecContract
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFree
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat4
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCertDefs
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.FlatBase
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecFree
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecHX3
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCertDefs` (sha256 2e386ba8ff5f32e1…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 18, step 4a): definitions for the certificate of a term with records

`TermCertWG` (`TermCertW` of the top level with the region as a parameter) and `termCertW_of_G`; `recW`, `recEng` (the weight record and engine datum of a term with records; their output box and set
are those of `natEng`); `exists_row_maps` (functions giving the pair row and branch row of every record).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The `TermCertW` of the top level with the region as a parameter (so that the transport `R'' = R` is a `subst`). -/
def TermCertWGΓ {A : ℝ} {P : WTParams} (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) (κ0 : KPar P.d)
    (R'' : CLRegionData G (LvlΓ.top B).c.U (LvlΓ.top B).c.a (LvlΓ.top B).c.b)
    (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞) : Prop :=
  ∃ (n' : ℕ) (hM9 : NormalChartSupply γF) (B' : CLChainAssemblyΓ γF G R'' n')
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B').TVar × (assemblyShapeΓ hM9 B').TVar)) (g g' : (assemblyShapeΓ hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatumΓ hM9 B' hG W wN wDec bk cons g g'))
    (Rw : ∀ ρ : Row (engDatumΓ hM9 B' hG W wN wDec bk cons g g'), RowData (engDatumΓ hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0),
    (∀ ρ, (Rw ρ).Ae Z.hI) ∧ (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) ∧
    W.wBar = κ0.base ∧
    Bx ⊆ outBox (engDatumΓ hM9 B' hG W wN wDec bk cons g g') ∧ K = outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η ∧
    (∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R'' P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u (LvlΓ.top B).c.a = t 0 → ψ (clExtendIndices R'' κ.1) t u = ψ (clExtendIndices R'' κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B (LvlΓ.top B)) (LeafNegΓ B (LvlΓ.top B)) t) u) ∧
    (∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign (LvlΓ.top B).c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign (LvlΓ.top B).c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B (LvlΓ.top B)) (LeafNegΓ B (LvlΓ.top B)) tt)
        ψ wN wDec bk cons g g' Z.Mx (allCR Rw)) ∧
    Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw ρ).b) ≤ β'

theorem termCertW_iff_GΓ {A : ℝ} {P : WTParams} (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) (κ0 : KPar P.d)
    (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞) :
    TermCertWΓ (A := A) B hG κ0 (LvlΓ.top B) ψ Bx K β' ↔ TermCertWGΓ (A := A) B hG κ0 (LvlΓ.top B).region ψ Bx K β' := Iff.rfl

theorem termCertW_of_GΓ {A : ℝ} {P : WTParams} (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) (κ0 : KPar P.d)
    (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞)
    (h : TermCertWGΓ (A := A) B hG κ0 R ψ Bx K β') : TermCertWΓ (A := A) B hG κ0 (LvlΓ.top B) ψ Bx K β' :=
  (termCertW_iff_GΓ B hG κ0 ψ Bx K β').2 ((top_region_eqΓ B).symm ▸ h)

/-- The weight/clock record of a term with records: `termW` with the record block kinds. -/
noncomputable abbrev recWΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop) (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) :
    SumintWeightClockData (assemblyShapeΓ hM9 B) d :=
  termWΓ hM9 B RD hG layer hLayer (recBkΓ B RD hG layer hM9 recs kd zc) (qOutOf RD hG layer a b R) centre wBar lam

/-- The engine datum of a term with records. -/
noncomputable abbrev recEngΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) : SumintPar.SumintDatum d :=
  engDatumΓ hM9 B hG (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam) (30 * d - 1) (30 * d)
    (recBkΓ B RD hG layer hM9 recs kd zc) (consXΓ hM9 B (layC RD hG layer) (bexOf recs) (recAddΓ B hM9 recs zc addr))
    (recGΓ B hM9 hG recs kd (rowCoupleGΓ hM9 B RD hG layer hLayer)) (rowTreeGΓ hM9 B RD hG layer hLayer)

theorem exists_row_mapsΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) (recs : List (ExcRec G d))
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (hbjI : ∀ r ∈ recs, r.bj ∈ clInteriorBranches R) :
    ∃ vpf vbf : ExcRec G d → (assemblyShapeΓ hM9 B).VIdx,
      (∀ r (hr : r ∈ recs), vpf r = assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩) ∧
      (∀ r (hr : r ∈ recs), vbf r = assemblyBranchBijΓ hM9 B ⟨r.bj, hbjI r hr⟩) := by
  classical
  have : Nonempty (assemblyShapeΓ hM9 B).VIdx :=
    ⟨WaveTurbulence.Sumint.timeVectorEquiv _ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)⟩
  have h1 : ∀ r, r ∈ recs → ∃ v : (assemblyShapeΓ hM9 B).VIdx, ∃ hr : r ∈ recs, v = assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩ :=
    fun r hr => ⟨_, hr, rfl⟩
  have h2 : ∀ r, r ∈ recs → ∃ v : (assemblyShapeΓ hM9 B).VIdx, ∃ hr : r ∈ recs, v = assemblyBranchBijΓ hM9 B ⟨r.bj, hbjI r hr⟩ :=
    fun r hr => ⟨_, hr, rfl⟩
  choose! vpf hvpf using h1
  choose! vbf hvbf using h2
  exact ⟨vpf, vbf, fun r hr => (hvpf r hr).choose_spec, fun r hr => (hvbf r hr).choose_spec⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
