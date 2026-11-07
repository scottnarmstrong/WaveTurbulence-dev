/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.GenKernel
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm

/-! # TARGET vineest Step 2 (V4 endpoint) with generic row weights (V5 Step 4d-A, item 3)

`vineChainGen_eq_sumintForm`: for an ARBITRARY factor `Φ κ t τ` in place of the native product
`clLocalStarProduct`, written (hypothesis `hΦ`, the shape of `clLocalStarProduct_eq_weights`) as a product over the
sumint rows of abstract row weights `WKg, WLg` evaluated at the coset-decoration momenta of the row's pair leaf and
branch, the recentered kernel is the `sumint` input form with those row weights.  With `Φ := clLocalStarProduct`,
`WKg := assemblyWK`, `WLg := assemblyWL` this is `vineChain_eq_sumintForm`.  The twisted vine's bundle (a finite sum of
products of two rows, with indicator constraints) is one choice of `Φ`; its two exceptional rows are two choices of
`WKg v`, `WLg v`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The generic row-weight factorization hypothesis (shape of `clLocalStarProduct_eq_weights`). -/
def RowFactorization (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) (L : ℝ) (base : Mom d)
    (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ) : Prop :=
  ∀ (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R),
    Φ κ t τ = ∏ v : (assemblyShape hM9 B).VIdx,
      (WKg v t τ (cosetDecoration G L base κ ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode) *
        WLg v t τ (cosetDecoration G L base κ (assemblyBranchOf hM9 B v).1.toNode))

/-- One summand of the recentered regional kernel in `sumint` form, generic rows. -/
theorem clLocalRecenteredSummandGen_sumint (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (layer0 : GBranch G.tree → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d) (hΦ : RowFactorization hM9 B hG L base Φ WKg WLg)
    (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalRecenteredSummandGen R Φ layer0 L γ δ base (fun j => base+latticePoint L (β j)) t
        ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layer0 t).indicator
          (fun τ => signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (WKg v t (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v t (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ) := by
  unfold clLocalRecenteredSummandGen
  congr 1
  by_cases h : assemblyClockEquiv hM9 B τ ∈ clLocalTimeDomain R layer0 t
  · have h' : τ ∈ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layer0 t := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ,
      ← assembly_regionalPhase_eq_signedPhase hM9 B hG W hpar hbad hL base β hβ γ δ η x t τ,
      hΦ]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl (fun v _ => ?_))
    rw [← assembly_pair_momentum hM9 B hG W hL base β hβ x v,
      ← assembly_branch_momentum hM9 B hG W hL base β hβ x v]
  · have h' : τ ∉ assemblyClockEquiv hM9 B ⁻¹' clLocalTimeDomain R layer0 t := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **TARGET vineest Step 2 (V4 endpoint), generic rows.** -/
theorem vineChainGen_eq_sumintForm (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (hG : G.IsPlain) (Φ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → CLInternalTime R → ℂ)
    (WKg WLg : (assemblyShape hM9 B).VIdx → (Fin 3 → ℝ) → CLInternalTime R → Mom d → ℂ)
    (layer0 : GBranch G.tree → ℕ) (W : SumintWeightClockData (assemblyShape hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d) (hΦ : RowFactorization hM9 B hG L base Φ WKg WLg)
    (hq : W.q = assemblyTimeQ hM9 B layer0)
    (hc : W.constraints = assemblyTimeConstraints hM9 B)
    (hb1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching)
    (hb2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching)
    (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (t : Fin 3 → ℝ) :
    clRecenteredLocalKernelGen R Φ layer0 L γ δ base (t 0) (t 1) (t 2)
      (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ),
        (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) *
        ∫ τ in (sourceSumintDatum hM9 B hG W).timeDom (assemblyShape_I_pos hM9 B) (t 0) (t 1) (t 2),
          signedPhase (sourceSumintDatum hM9 B hG W)
              (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (WKg v t (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              WLg v t (assemblyClockEquiv hM9 B τ)
                ((sourceSumintDatum hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v)) := by
  rw [clLocalKernelGen_reindexed hL hM9 B Φ layer0 γ δ base β hβ t]
  congr 1
  refine tsum_congr (fun x => ?_)
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun τ =>
    clLocalRecenteredSummandGen_sumint hM9 B hG Φ WKg WLg layer0 W hpar hbad hL γ δ η base hΦ β hβ x t τ)),
    integral_const_mul,
    integral_clockDomain_eq hM9 B (assemblyShape_I_pos hM9 B) _ t hb1 hb2,
    ← timeDom_eq_assemblyTimeDomain hM9 B hG W _ hq hc]
  rfl

end WaveTurbulence.VineEstS5A
