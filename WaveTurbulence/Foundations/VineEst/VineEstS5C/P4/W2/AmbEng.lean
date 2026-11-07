/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Datum
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Cph
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AdmissibleAssembly

/-! # P4-W2 (session 9, step 4): the ambient engine data `AmbW` of an engine datum

`structAdm_engDatum`: the structural part of admissibility of `engDatum hM9 B hG W wN wDec bk cons g g'` (from `sourceSumintDatum_algebraic_hypotheses` and the layer bounds).
`ambW_engDatum`: the `AmbW` of the engine datum from `AmbP`, the structural part, the bad-case clause `BadClauseP`, a sign mixture, the kind-2 unit-gap bound and `d < wDec`, `M ≤ N₁⁴`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The algebraic clauses at the exact frozen datum, for every `A ≥ 6561`. -/
theorem sourceAlgebraic_ge (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {A : ℝ} (hA : 6561 ≤ A) :
    SumintAlgebraicHypotheses (sourceSumintDatum hM9 B hG W) A := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sourceSumintDatum_algebraic_hypotheses hM9 B hG W
  exact ⟨h1, h2, h3.trans (pow_le_pow_left₀ (by norm_num) hA _), h4, h5, h6⟩

/-- **The structural admissibility of the engine datum.** -/
theorem structAdm_engDatum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {A L γ η : ℝ} (hA : 6561 ≤ A) {Dsteps : ℕ}
    (hq : ∀ v, W.q v + 1 ≤ Dsteps) (hqo : ∀ c, W.qOut c + 1 ≤ Dsteps) (wN wDec : ℕ) (hN : d + 1 ≤ wN) (hD : d < wDec)
    (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ) :
    StructAdm (engDatum hM9 B hG W wN wDec bk cons g g') A L γ η Dsteps :=
  structAdm_modPiece (structAdm_of_algebraic (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B)
    wN wDec (sourceAlgebraic_ge hM9 B hG W hA) hq hqo hN hD) _ _ _ _

/-- **`AmbW` of the engine datum** from the ambient parameter facts, the structural admissibility, the bad-case clause, a sign mixture,
the kind-2 unit-gap bound (`hqq`: the two clocks of a kind-2 block have layers at distance `≤ g`), `d < wDec` and `M ≤ N₁⁴`. -/
noncomputable def ambW_engDatum {A : ℝ} {P : WTParams} (Z0 : AmbP A P) (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (wN wDec : ℕ)
    (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (hS : StructAdm (engDatum hM9 B hG W wN wDec bk cons g g') A P.L P.γ P.η P.D)
    (hbad : BadClauseP (engDatum hM9 B hG W wN wDec bk cons g g'))
    (Mx : CharMix (assemblyShape hM9 B) P.d) (gap : ℝ) (hgap : 0 ≤ gap)
    (hqq : ∀ i (h : (engDatum hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
        (engDatum hM9 B hG W wN wDec bk cons g g').badKind i = 2 ∧ 0 < (engDatum hM9 B hG W wN wDec bk cons g g').S.m i),
      |(((engDatum hM9 B hG W wN wDec bk cons g g').q (.inl ⟨i, ⟨1, by omega⟩⟩) : ℕ) : ℝ) -
        (((engDatum hM9 B hG W wN wDec bk cons g g').q (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩)) : ℕ) : ℝ)| ≤ gap)
    (hreg : P.d < wDec) (hM : (assemblyShape hM9 B).M ≤ P.N 1 ^ 4) :
    AmbW A P (engDatum hM9 B hG W wN wDec bk cons g g') where
  toAmbP := Z0
  hI := assemblyShape_I_pos hM9 B
  Mx := Mx
  Cph := cphConst (engDatum hM9 B hG W wN wDec bk cons g g') P.η gap
  hCph0 := cphConst_nonneg _ _ _
  hCph := hCph_of_q _ (assemblyShape_I_pos hM9 B) P.η gap hgap (by have := Z0.hη3; linarith) hqq
  hreg := hreg
  hAdm := hAdm_of_struct hS hbad
  hM := hM

end WaveTurbulence.VineEstS5C.P4.W2
