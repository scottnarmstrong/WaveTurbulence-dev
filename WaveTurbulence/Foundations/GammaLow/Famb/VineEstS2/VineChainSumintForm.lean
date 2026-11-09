/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2TimeS1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm` (sha256 29c7604e3b9062e8…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # TARGET vineest Step 2: the vine-chain contribution in `sumint` input form

`vineChain_eq_sumintForm` identifies the actual recentered regional kernel of a vine chain
(the expression `\widetilde K` of TARGET (tildeK2)) with

`coupling^{n₁} ζ ∑ₓ ε(x) ∫_{timeDom(q,constraints)} signedPhase(D)(x,r,t,τ) ∏ᵥ 𝒦ᵥ(kᵥ) ℒᵥ(ℓᵥ)`,

where `D = sourceSumintDatum` is the frozen `sumint` datum of the chain, `kᵥ = D.kVec`,
`ℓᵥ = D.ℓVec` are evaluated at the boundary vector `sumintBoundary ζ (base + β)`, `timeDom` is
the frozen `sumint` time domain with `q` the source layers and the constraints the parent order,
and `𝒦ᵥ, ℒᵥ` are the actual starred kernels `K_Q^*, K_T^*` of the garden (time dependent; their
expansion into time-independent weights is TARGET Step 3). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- One summand of the recentered regional kernel in `sumint` form. -/
theorem clLocalRecenteredSummand_sumintΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (D : ReconstructionData G) (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hpar : ∀ v, W.param v = 0) (hbad : ∀ i, W.badKind i ≠ 2)
    {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clLocalRecenteredSummand D hG R L γ δ F layer hLayer base (fun j => base+latticePoint L (β j)) t
        ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) (assemblyClockEquivΓ hM9 B τ) =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) : ℂ) *
        ((assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R
            (fun v => layer (D.coreBranch hG v).toNode) t).indicator
          (fun τ => signedPhase (sourceSumintDatumΓ hM9 B hG W)
              (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2*δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
            ∏ v, (assemblyWKΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).kVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v) *
              assemblyWLΓ hM9 B D hG L γ δ F layer hLayer t (assemblyClockEquivΓ hM9 B τ) v
                ((sourceSumintDatumΓ hM9 B hG W).ℓVec L x
                  (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v))) τ) := by
  unfold clLocalRecenteredSummand
  congr 1
  by_cases h : assemblyClockEquivΓ hM9 B τ ∈ clLocalTimeDomain R
      (fun v => layer (D.coreBranch hG v).toNode) t
  · have h' : τ ∈ assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ,
      ← assembly_regionalPhase_eq_signedPhaseΓ hM9 B hG W hpar hbad hL base β hβ γ δ η x t τ,
      clLocalStarProduct_eq_weightsΓ hM9 B D hG L γ δ F layer hLayer base]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl (fun v _ => ?_))
    rw [← assembly_pair_momentumΓ hM9 B hG W hL base β hβ x v,
      ← assembly_branch_momentumΓ hM9 B hG W hL base β hβ x v]
  · have h' : τ ∉ assemblyClockEquivΓ hM9 B ⁻¹' clLocalTimeDomain R
        (fun v => layer (D.coreBranch hG v).toNode) t := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end WaveTurbulence.GammaLow.Famb.VineEstS2
