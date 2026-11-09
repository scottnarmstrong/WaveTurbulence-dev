/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixIdentities
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedInverseMatrix
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLInverseMatrixIdentities
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedInverseMatrix` (sha256 503bfd2d54d91c2a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact unit inverse after the frozen gap-sign lattice involution -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def normalizedInversePairMatrixΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    Matrix (assemblyShapeΓ hM9 B).VIdx (assemblyShapeΓ hM9 B).VIdx ℤ :=
  jointSignMatrix _ * assemblyInversePairMatrixΓ hM9 B hG

theorem normalizedPairMatrix_eq_mulΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    normalizedPairMatrixΓ hM9 B hG = assemblyPairMatrixΓ hM9 B hG * jointSignMatrix _ := by
  classical
  ext v j
  simp only [normalizedPairMatrixΓ,jointSignMatrix,Matrix.mul_diagonal]

theorem normalizedInversePairMatrix_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v p : (assemblyShapeΓ hM9 B).VIdx) : IsUnitCoeff (normalizedInversePairMatrixΓ hM9 B hG v p) := by
  classical
  change IsUnitCoeff ((Matrix.diagonal (jointFlipSign (assemblyShapeΓ hM9 B)) * assemblyInversePairMatrixΓ hM9 B hG) v p)
  rw [Matrix.diagonal_mul,mul_comm]
  exact jointFlip_unit _ _ _ (assemblyInversePairMatrix_unitΓ hM9 B hG v p)

theorem normalizedPairMatrix_mul_inverseΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    normalizedPairMatrixΓ hM9 B hG * normalizedInversePairMatrixΓ hM9 B hG = 1 := by
  rw [normalizedPairMatrix_eq_mulΓ,normalizedInversePairMatrixΓ,← Matrix.mul_assoc,
    Matrix.mul_assoc (assemblyPairMatrixΓ hM9 B hG),jointSignMatrix_square,Matrix.mul_one,
    assemblyPairMatrix_mul_inverseΓ]

theorem normalizedInversePairMatrix_mulΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) :
    normalizedInversePairMatrixΓ hM9 B hG * normalizedPairMatrixΓ hM9 B hG = 1 :=
  mul_eq_one_comm.mp (normalizedPairMatrix_mul_inverseΓ hM9 B hG)

end WaveTurbulence.GammaLow.Famb.VineEstS2
