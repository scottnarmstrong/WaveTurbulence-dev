/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNodeBonds
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintPredecessors
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintPredecessors
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintMatrices` (sha256 2c584f69560233d4…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Literal source pair and branch decoder matrices on sumint rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyPairMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  fun v j => chainDecodeFreeΓ hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v))
    ((assemblyVectorEquivΓ hM9 B).symm j)

noncomputable def assemblyBranchMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  fun v j => chainDecodeFreeΓ hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v))
    ((assemblyVectorEquivΓ hM9 B).symm j)

theorem assemblyPairMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v j : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (assemblyPairMatrixΓ hM9 B hG v j) :=
  chainDecodeFree_unitΓ hM9 B _ _

theorem assemblyBranchMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v j : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (assemblyBranchMatrixΓ hM9 B v j) :=
  chainDecodeFree_unitΓ hM9 B _ _

end WaveTurbulence.GammaLow.Famb.VineEstS2
