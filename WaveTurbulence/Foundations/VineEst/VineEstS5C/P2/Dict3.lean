/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict2

/-! # P2: `termFnR = c ζ · clockedExprMul3` and the bound of the recentered term (dictionary, assembled)

`termFnR_eq_expr3`: `recFac · c ζ · lkRaw ψ = c ζ · clockedExprMul3 Mx cr` at the boundary `E = sumintBoundary σ (w̲ + β)`, from the generic `sumint` form
(`Dict`), the engine identification (`Dict2`).  `exprBound_of_engine`: the resulting bound of the recentered observable on `outBox × outSet` by
`‖c ζ‖ · XNorm00Restr(clockedExprMul3)`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem termFnR_eq_expr3 (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → Mom d → ℂ)
    (WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (layer0 : GBranch G.tree → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d) (hΦ : RowFactorizationR hM9 B hG L base Φ WKg WLg)
    (hq : W.q = assemblyTimeQ hM9 B layer0) (hc : W.constraints = assemblyTimeConstraints hM9 B)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (hψ : ∀ (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (t : Fin 3 → ℝ) (τ : CLInternalTime R),
      ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = clLocalSummandGen R Φ layer0 L γ δ base β' t κ τ)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hD : DictHyp hM9 B hG W hL γ δ η base β hβ tt WKg WLg wN wDec bk cons g g' Mx cr) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      ((coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base ψ tt (sumintBoundary (G.sign a.toNode)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))))) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprMul3 Mx cr (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  rw [recFac_cst_lkRaw_eq hM9 B hG Φ WKg WLg layer0 W hpar hbad hL γ δ η base hΦ hq hc hb1 hb2 ψ hψ β hβ tt]
  congr 1
  exact sumint_eq_expr3 hM9 B hG W hL γ δ η base β hβ tt WKg WLg wN wDec bk cons g g' Mx cr hD.1 hD.2.1 hD.2.2.1 hD.2.2.2

open scoped ENNReal in
/-- **The recentered observable of a term is bounded by `‖c ζ‖ ·` the clocked expression** on the output box and set of the engine datum. -/
theorem recBound_of_engine {P : WTParams} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (Φ : (GNode G.tree → (Fin P.d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom P.d → Mom P.d → ℂ)
    (WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom P.d → ℂ)
    (layer0 : GBranch G.tree → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) P.d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    (hL : P.L ≠ 0) (hΦ : RowFactorizationR hM9 B hG P.L W.wBar Φ WKg WLg)
    (hq : W.q = assemblyTimeQ hM9 B layer0) (hc : W.constraints = assemblyTimeConstraints hM9 B)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (ψ : (GNode G.tree → (Fin P.d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (hψ : ∀ (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R P.L W.wBar β') (t : Fin 3 → ℝ) (τ : CLInternalTime R),
      ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = clLocalSummandGen R Φ layer0 P.L P.γ P.δ W.wBar β' t κ τ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) P.d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hD : ∀ tt ∈ outBox (engDatum hM9 B hG W wN wDec bk cons g g'), ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B hG W wN wDec bk cons g g') P.L P.γ P.η →
      DictHyp hM9 B hG W hL P.γ P.δ P.η W.wBar β hβ tt WKg WLg wN wDec bk cons g g' Mx cr) :
    XNorm00Restr (2 * P.η ^ 8) (outBox (engDatum hM9 B hG W wN wDec bk cons g g'))
        (outSet (engDatum hM9 B hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => recFac (G.sign a.toNode) (G.sign a.toNode) P.L P.γ P.δ tt E *
          ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
            lkRaw R P.L W.wBar ψ tt (sumintBoundary (G.sign a.toNode) E))) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ *
        XNorm00Restr (2 * P.η ^ 8) (outBox (engDatum hM9 B hG W wN wDec bk cons g g'))
          (outSet (engDatum hM9 B hG W wN wDec bk cons g g') P.L P.γ P.η)
          (fun tt E => clockedExprMul3 Mx cr (assemblyShape_I_pos hM9 B) P.L P.γ (2 * P.δ) P.η tt E) := by
  refine (XNorm00Restr_mono_of_eq _ _ _ _ (fun tt E => (coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
    clockedExprMul3 Mx cr (assemblyShape_I_pos hM9 B) P.L P.γ (2 * P.δ) P.η tt E) ?_).trans
    (VineEstS3.Eng.XNorm00Restr_const_mul_le _ _ _ _ _)
  intro tt htt E hE
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  have := termFnR_eq_expr3 hM9 B hG Φ WKg WLg layer0 W hpar hbad hL P.γ P.δ P.η W.wBar hΦ hq hc hb1 hb2 ψ hψ β hβ tt
    wN wDec bk cons g g' Mx cr (hD tt htt β hβ hE)
  exact this

end WaveTurbulence.VineEstS5C.P2
