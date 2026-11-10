/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintJointFlip
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintMatrices
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates` (sha256 b27d1c245142791c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Regional lattice coordinates with the frozen sumint gap convention -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def clNormalizedChainEquivΓ {L : ℝ} (hL : L ≠ 0)
    (B : CLChainAssemblyΓ γF G R n) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (hM9 : NormalChartSupply γF) :
    CLLocalDecoration R L base (fun j => base+latticePoint L (β j)) ≃
      ((assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :=
  (clChainCoordinateEquivΓ hL B base β hβ hM9).trans (jointFlip _)

noncomputable def normalizedPairMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  fun v j => assemblyPairMatrixΓ hM9 B hG v j * jointFlipSign _ j

noncomputable def normalizedBranchMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  fun v j => assemblyBranchMatrixΓ hM9 B v j * jointFlipSign _ j

theorem normalizedPairMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v j : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (normalizedPairMatrixΓ hM9 B hG v j) :=
  jointFlip_unit _ _ _ (assemblyPairMatrix_unitΓ hM9 B hG v j)

theorem normalizedBranchMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v j : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (normalizedBranchMatrixΓ hM9 B v j) :=
  jointFlip_unit _ _ _ (assemblyBranchMatrix_unitΓ hM9 B v j)

end WaveTurbulence.GammaLow.Famb.VineEstS2
