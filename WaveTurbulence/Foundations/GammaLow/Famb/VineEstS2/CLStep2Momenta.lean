/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintBoundaryNormalization
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLGlobalPhase
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta` (sha256 5fb81e2d329439e2…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # TARGET Step 2: the sumint vectors `k_v`, `ℓ_v` are the actual source momenta

For the source sumint datum, the frozen affine forms `kVec` / `ℓVec` evaluated at the
normalized lattice point `x` and at the boundary vector `sumintBoundary ζ (base + β)` are the
physical coset momenta of the first leaf of the `v`-th regional pair, respectively of the
`v`-th interior branch. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The regional pair carried by the `v`-th sumint row. -/
noncomputable def assemblyPairOfΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) : ↥(clRegionalPairs hG U) :=
  (assemblyPairOrderΓ hG B hM9).symm ((assemblyRowEquivΓ hM9 B).symm v)

/-- The interior branch carried by the `v`-th sumint row. -/
noncomputable def assemblyBranchOfΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : ↥(clInteriorBranches R) :=
  (assemblyIntOrderΓ hM9 B).e.symm ((assemblyRowEquivΓ hM9 B).symm v)

theorem assembly_pair_momentumΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    cosetDecoration G L base
        (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)
        ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode =
      (sourceSumintDatumΓ hM9 B hG W).kVec L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v := by
  have h := clChain_pair_affine_valueΓ hL B base β hβ hM9 hG (jointFlip _ x) v
  have hv : assemblyPairValueΓ hM9 B hG
      (clExtendIndices R ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm (jointFlip _ x)).1) v =
      clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
        ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode := by
    exact congrArg (fun z => clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 z)
      (clPairFirstLeaf_node B.isBlock R hG (assemblyPairOfΓ hM9 B hG v))
  have hb := sumintBoundary_lower (G.sign a.toNode) (fun j => base + latticePoint L (β j))
  unfold cosetDecoration SumintDatum.kVec
  rw [← hv, h]
  exact (affine_row_physical L base β _ hb.1 hb.2 _ (fun j => assemblyPairMatrixΓ hM9 B hG v j)
    (fun j => jointFlipSign _ j) x).symm

theorem assembly_branch_momentumΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    cosetDecoration G L base
        (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)
        (assemblyBranchOfΓ hM9 B v).1.toNode =
      (sourceSumintDatumΓ hM9 B hG W).ℓVec L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v := by
  have h := clChain_branch_affine_valueΓ hL B base β hβ hM9 (jointFlip _ x) v
  have hv : assemblyBranchValueΓ hM9 B
      (clExtendIndices R ((clChainCoordinateEquivΓ hL B base β hβ hM9).symm (jointFlip _ x)).1) v =
      clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1
        (assemblyBranchOfΓ hM9 B v).1.toNode := rfl
  have hb := sumintBoundary_lower (G.sign a.toNode) (fun j => base + latticePoint L (β j))
  unfold cosetDecoration SumintDatum.ℓVec
  rw [← hv, h]
  exact (affine_row_physical L base β _ hb.1 hb.2 _ (fun j => assemblyBranchMatrixΓ hM9 B v j)
    (fun j => jointFlipSign _ j) x).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
