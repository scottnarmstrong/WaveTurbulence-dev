/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Datum
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.LevelAbs

/-! # P2: the `sumint` form is the clocked expression of the piece datum (`termFn = clockedExprMul3`, second half)

`engDatum`: the piece datum of the assembly (`modPiece (pieceDatum (sourceSumintDatum ..) ..) bk cons g g'`).  `sumint_eq_expr3`: the `sumint` form of
`Dict.recFac_cst_lkRaw_eq` equals `c ζ · clockedExprMul3 Mx cr` as soon as (`hint`) the engine integrand times the kind-1 prefactor is the `sumint` integrand
a.e. on the engine time domain, (`hsub`) the engine domain is contained in the `sumint` domain and (`hvan`) the `sumint` integrand vanishes a.e. on the rest. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The engine datum of a piece of the assembly. -/
noncomputable def engDatum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (g g' : (assemblyShape hM9 B).VIdx → ℕ) : SumintPar.SumintDatum d :=
  modPiece (pieceDatum (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) wN wDec) bk cons g g'

/-- The kind-1 prefactor `‖E₀ - E₁‖^{#kind-1 blocks}` of `clockedExprMul3`. -/
noncomputable def kind1Pref {D : SumintPar.SumintDatum d} (E : Fin 4 → Mom d) : ℝ :=
  ‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card

/-- **The `sumint` form is `c ζ · clockedExprMul3`** under the three pointwise hypotheses (see the module docstring). -/
theorem sumint_eq_expr3 (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → Mom d → ℂ)
    (WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d)
    (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ))
    (hint : ∀ x, ∀ᵐ τ ∂(volume.restrict ((engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B)
        (tt 0) (tt 1) (tt 2))),
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
        clockedIntegrand3 cr L γ (2 * δ) η x (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ =
      signedPhase (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
        ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
            ((sourceSumintDatum hM9 B hG W).kVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
          WLg v tt (assemblyClockEquiv hM9 B τ)
            ((sourceSumintDatum hM9 B hG W).ℓVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))
    (hsub : (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) ⊆
      (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2))
    (hvan : ∀ x, ∀ᵐ τ ∂volume, τ ∈ (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      τ ∉ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      signedPhase (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
        ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
            ((sourceSumintDatum hM9 B hG W).kVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
          WLg v tt (assemblyClockEquiv hM9 B τ)
            ((sourceSumintDatum hM9 B hG W).ℓVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)) = 0) :
    (∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
          (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
          ∫ τ in (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2),
            signedPhase (sourceSumintDatum hM9 B hG W)
                (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
                (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                  sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
              ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
                  ((sourceSumintDatum hM9 B hG W).kVec L x
                    (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
                WLg v tt (assemblyClockEquiv hM9 B τ)
                  ((sourceSumintDatum hM9 B hG W).ℓVec L x
                    (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) =
      clockedExprMul3 Mx cr (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  unfold clockedExprMul3
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  have key := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume)
    (WaveTurbulence.VineEstS3.Eng.measurableSet_timeDom (sourceSumintDatum hM9 B hG W) (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2)).nullMeasurableSet hsub
    (f := fun τ => signedPhase (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
        ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
            ((sourceSumintDatum hM9 B hG W).kVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
          WLg v tt (assemblyClockEquiv hM9 B τ)
            ((sourceSumintDatum hM9 B hG W).ℓVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)))
    (by filter_upwards [hvan x] with τ h hτ; exact h hτ.1 hτ.2)
  rw [← hMx x, key]
  erw [integral_congr_ae ((hint x).mono fun τ h => h.symm), integral_const_mul]
  unfold kind1Pref
  exact mul_left_comm _ _ _

open Classical in
/-- The four pointwise hypotheses of `sumint_eq_expr3` at the exterior clocks `tt` and the integer boundary `β`. -/
def DictHyp (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (WKg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → Mom d → ℂ)
    (WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d)
    (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g')) : Prop :=
  (∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ)) ∧
  (∀ x, ∀ᵐ τ ∂(volume.restrict ((engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B)
        (tt 0) (tt 1) (tt 2))),
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
        clockedIntegrand3 cr L γ (2 * δ) η x (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ =
      signedPhase (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
        ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
            ((sourceSumintDatum hM9 B hG W).kVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
          WLg v tt (assemblyClockEquiv hM9 B τ)
            ((sourceSumintDatum hM9 B hG W).ℓVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) ∧
  ((engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) ⊆
      (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2)) ∧
  (∀ x, ∀ᵐ τ ∂volume, τ ∈ (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      τ ∉ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      signedPhase (sourceSumintDatum hM9 B hG W) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ *
        ∏ v, (WKg v tt (assemblyClockEquiv hM9 B τ) (bgap (G.sign a.toNode) L base β)
            ((sourceSumintDatum hM9 B hG W).kVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
          WLg v tt (assemblyClockEquiv hM9 B τ)
            ((sourceSumintDatum hM9 B hG W).ℓVec L x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)) = 0)

end WaveTurbulence.VineEstS5C.P2
