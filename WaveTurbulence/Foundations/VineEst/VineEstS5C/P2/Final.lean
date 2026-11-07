/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict4
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceRem

/-! # P2 EXPORT: `termBoundR_of_piece` and `lkAbs_of_piece` (V5 Step 4d part C, step 7)

`TermData`: the dictionary data of one summand `ψ` of the local sum-integral of the region `R` (the factor `Φ`, the `r`-dependent row weights, the V4 weight
data `W`, the generic-summand identity `hψ`, the datum numerals of the engine datum `engDatum`).  `DictAll`: for every pair of rows `(K, L)` of the operative vine with
the weights/slots `(Kw, Ks, Lw, Ls)` the `DictHyp` identification of the merged engine rows with `ψ` at every integer boundary of the output set.
`termBoundR_of_piece`: a `PieceBound` (the `piece_*` theorems) and `DictAll` give the bound of the RECENTERED observable
`recFac · c ζ lkRaw ψ` by `‖c ζ‖ · pre · bK · bL · others`.  `lkAbs_of_piece`: the absolute convergence `P3.LkAbs` of `ψ` at the boundary of every point of the output set. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The dictionary data of a summand `ψ` over the assembly `B` of the region `R` (the parameters are those of `P`). -/
structure TermData (P : WTParams) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) where
  Φ : (GNode G.tree → (Fin P.d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ
  WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom P.d → Mom P.d → ℂ
  WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom P.d → ℂ
  layer0 : GBranch G.tree → ℕ
  W : SumintWeightClockData (assemblyShape hM9 B) P.d
  hpar : ∀ v, W.param v = 0
  hbad : ∀ i, W.badKind i ≠ 2
  hL : P.L ≠ 0
  hΦ : RowFactorizationR hM9 B hG P.L W.wBar Φ WKg WLg
  hq : W.q = assemblyTimeQ hM9 B layer0
  hc : W.constraints = assemblyTimeConstraints hM9 B
  hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching
  hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching
  ψ : (GNode G.tree → (Fin P.d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ
  hψ : ∀ (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R P.L W.wBar β') (t : Fin 3 → ℝ) (τ : CLInternalTime R),
    ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = clLocalSummandGen R Φ layer0 P.L P.γ P.δ W.wBar β' t κ τ
  wN : ℕ
  wDec : ℕ
  bk : Fin (assemblyShape hM9 B).I → Fin 4
  cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)
  g : (assemblyShape hM9 B).VIdx → ℕ
  g' : (assemblyShape hM9 B).VIdx → ℕ

variable {A : ℝ} {P : WTParams} {hM9 : VINEPARAM} {B : CLChainAssembly G R n} {hG : G.IsPlain}

/-- The engine datum of the term. -/
noncomputable abbrev TermData.D (T : TermData P hM9 B hG) : SumintPar.SumintDatum P.d :=
  engDatum hM9 B hG T.W T.wN T.wDec T.bk T.cons T.g T.g'

/-- The identification of the merged engine rows with the term `ψ`, for every pair of rows with the given weights and slots, at every integer
boundary of the output set. -/
def DictAll (T : TermData P hM9 B hG) (Z : Amb A P T.D)
    (Kw Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ) (Ks Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot T.D) : Prop :=
  ∀ (K : RowData T.D (6 * P.η ^ 6) (Sum.inl Z.v0)) (L : RowData T.D (6 * P.η ^ 6) (Sum.inr Z.v0)),
    (∀ c r k, K.W c r k = Kw c r k) → (∀ i, K.slot i = Ks i) → (∀ c r k, L.W c r k = Lw c r k) → (∀ i, L.slot i = Ls i) →
    ∀ tt ∈ outBox T.D, ∀ (β : Fin 4 → (Fin P.d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign a.toNode) (fun j => T.W.wBar + latticePoint P.L (β j)) ∈ outSet T.D P.L P.γ P.η →
      DictHyp hM9 B hG T.W T.hL P.γ P.δ P.η T.W.wBar β hβ tt T.WKg T.WLg T.wN T.wDec T.bk T.cons T.g T.g' Z.Mx
        (mergeCR Z.cr0 Z.v0 K L)

/-- **`termBound_of_pieces` (recentered, one term).**  A `PieceBound` for the operative vine and the dictionary `DictAll` bound the recentered observable of the term
`ψ` on `outBox × outSet` of the engine datum. -/
theorem termBoundR_of_piece (T : TermData P hM9 B hG) (Z : Amb A P T.D)
    {Kw Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {Ks Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot T.D} {bK bL : ℝ≥0∞}
    (hP : PieceBound Z Kw Ks Lw Ls bK bL) (hD : DictAll T Z Kw Lw Ks Ls) :
    XNorm00Restr (2 * P.η ^ 8) (outBox T.D) (outSet T.D P.L P.γ P.η)
        (fun tt E => recFac (G.sign a.toNode) (G.sign a.toNode) P.L P.γ P.δ tt E *
          ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
            lkRaw R P.L T.W.wBar T.ψ tt (sumintBoundary (G.sign a.toNode) E))) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ * (Z.pre * (bK * bL * Z.others)) := by
  obtain ⟨K, L, h1, h2, h3, h4, hKae, hLae, hb⟩ := hP
  exact (recBound_of_engine hM9 B hG T.Φ T.WKg T.WLg T.layer0 T.W T.hpar T.hbad T.hL T.hΦ T.hq T.hc T.hb1 T.hb2 T.ψ T.hψ
    T.wN T.wDec T.bk T.cons T.g T.g' Z.Mx (mergeCR Z.cr0 Z.v0 K L)
    (fun tt htt β hβ hE => hD K L h1 h2 h3 h4 tt htt β hβ hE)).trans (mul_le_mul' le_rfl hb)

/-- **Absolute convergence of the term** (`P3.LkAbs`) at the boundary of every point of the output set. -/
theorem lkAbs_of_piece (T : TermData P hM9 B hG) (Z : Amb A P T.D)
    {Kw Lw : (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {Ks Ls : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot T.D} {bK bL : ℝ≥0∞}
    (hP : PieceBound Z Kw Ks Lw Ls bK bL) (hD : DictAll T Z Kw Lw Ks Ls) :
    ∀ tt ∈ outBox T.D, ∀ E ∈ outSet T.D P.L P.γ P.η,
      P3.LkAbs R P.L T.W.wBar T.ψ tt (sumintBoundary (G.sign a.toNode) E) := by
  obtain ⟨K, L, h1, h2, h3, h4, hKae, hLae, hb⟩ := hP
  intro tt htt E hE
  have hAbs := vineLevel_abs Z.hL Z.hη0 Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.cr0 Z.M0 Z.v0 K L hKae hLae Z.h0 tt htt E hE
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta T.hL (G.sign a.toNode) T.W.wBar E (fun c => (hE.1 c).1) hE.2.1
  exact lkAbs_of_exprAbs hM9 B hG T.Φ T.WKg T.WLg T.layer0 T.W T.hpar T.hbad T.hL P.γ P.δ P.η T.W.wBar T.hΦ T.hq T.hc T.hb1 T.hb2
    T.ψ T.hψ β hβ tt T.wN T.wDec T.bk T.cons T.g T.g' Z.Mx (mergeCR Z.cr0 Z.v0 K L)
    (hD K L h1 h2 h3 h4 tt htt β hβ hE) hAbs

end WaveTurbulence.VineEstS5C.P2
