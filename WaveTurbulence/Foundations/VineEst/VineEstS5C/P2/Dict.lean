/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.GenSumintR
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel

/-! # P2: the value dictionary `termFnR = c ζ · (sumint form)` (V5 Step 4d part C, `termFn = clockedExprMul3`, first half)

`recFac_cst_lkRaw_eq`: for a summand `ψ` that is the generic local summand of a factor `Φ` (`hψ`) with the `r`-dependent row factorization
`hΦ : RowFactorizationR`, the recentered observable `recFac · c ζ lkRaw ψ` at the boundary `E = sumintBoundary σ (w̲ + β)` is
`c ζ ∑'_x ε(x) ∫_{𝒟} signedPhase · ∏_v (WKg v … · WLg v …)`, the `sumint` form of V4 (`vineChainGenR_eq_sumintForm`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem vec3_eta' (tt : Fin 3 → ℝ) : ![tt 0, tt 1, tt 2] = tt := by
  ext i; fin_cases i <;> rfl

theorem vec4_eta'' {E : Type*} (v : Fin 4 → E) : ![v 0, v 1, v 2, v 3] = v := by
  ext i; fin_cases i <;> rfl

/-- `c ζ · lkRaw ψ` is the generic local kernel of `Φ` when `ψ` is the generic local summand. -/
theorem cst_lkRaw_eq_kernelGen (L γ δ : ℝ) (base : Mom d)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ) (layer0 : GBranch G.tree → ℕ)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (hψ : ∀ (β' : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β') (t : Fin 3 → ℝ) (τ : CLInternalTime R),
      ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = clLocalSummandGen R Φ layer0 L γ δ base β' t κ τ)
    (tt : Fin 3 → ℝ) (β' : Fin 4 → Mom d) :
    (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R * lkRaw R L base ψ tt β' =
      clLocalKernelGen R Φ layer0 L γ δ base (tt 0) (tt 1) (tt 2) (β' 0) (β' 1) (β' 2) (β' 3) := by
  unfold clLocalKernelGen lkRaw
  rw [vec3_eta', vec4_eta'']
  congr 1
  refine tsum_congr fun κ => ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ => hψ β' κ tt τ)

/-- **The recentered observable of a generic summand is the `sumint` form** (`vineChainGenR_eq_sumintForm`). -/
theorem recFac_cst_lkRaw_eq (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
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
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      ((coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base ψ tt (sumintBoundary (G.sign a.toNode)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))))) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
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
                    (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)) := by
  rw [← vineChainGenR_eq_sumintForm hM9 B hG Φ WKg WLg layer0 W hpar hbad hL γ δ η base hΦ hq hc hb1 hb2 β hβ tt,
    sumintBoundary_invol, cst_lkRaw_eq_kernelGen L γ δ base Φ layer0 ψ hψ tt]
  unfold clRecenteredLocalKernelGen recFac
  simp only [sumintBoundary_invol]

end WaveTurbulence.VineEstS5C.P2
