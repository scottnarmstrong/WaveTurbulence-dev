/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixIdentities
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates

/-! # Exact unit inverse after the frozen gap-sign lattice involution -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem jointFlipSign_square (S : SumintShape) (v : S.VIdx) : jointFlipSign S v*jointFlipSign S v = 1 := by
  unfold jointFlipSign
  split <;> norm_num

noncomputable def jointSignMatrix (S : SumintShape) : Matrix S.VIdx S.VIdx ℤ := by
  classical
  exact Matrix.diagonal (jointFlipSign S)

theorem jointSignMatrix_square (S : SumintShape) : jointSignMatrix S*jointSignMatrix S = 1 := by
  classical
  unfold jointSignMatrix
  rw [Matrix.diagonal_mul_diagonal]
  simp only [jointFlipSign_square,Matrix.diagonal_one]

noncomputable def normalizedInversePairMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  jointSignMatrix _ * assemblyInversePairMatrix hM9 B hG

theorem normalizedPairMatrix_eq_mul (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    normalizedPairMatrix hM9 B hG = assemblyPairMatrix hM9 B hG * jointSignMatrix _ := by
  classical
  ext v j
  simp only [normalizedPairMatrix,jointSignMatrix,Matrix.mul_diagonal]

theorem normalizedInversePairMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v p : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (normalizedInversePairMatrix hM9 B hG v p) := by
  classical
  change IsUnitCoeff ((Matrix.diagonal (jointFlipSign (assemblyShape hM9 B)) * assemblyInversePairMatrix hM9 B hG) v p)
  rw [Matrix.diagonal_mul,mul_comm]
  exact jointFlip_unit _ _ _ (assemblyInversePairMatrix_unit hM9 B hG v p)

theorem normalizedPairMatrix_mul_inverse (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    normalizedPairMatrix hM9 B hG * normalizedInversePairMatrix hM9 B hG = 1 := by
  rw [normalizedPairMatrix_eq_mul,normalizedInversePairMatrix,← Matrix.mul_assoc,
    Matrix.mul_assoc (assemblyPairMatrix hM9 B hG),jointSignMatrix_square,Matrix.mul_one,
    assemblyPairMatrix_mul_inverse]

theorem normalizedInversePairMatrix_mul (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    normalizedInversePairMatrix hM9 B hG * normalizedPairMatrix hM9 B hG = 1 :=
  mul_eq_one_comm.mp (normalizedPairMatrix_mul_inverse hM9 B hG)

end WaveTurbulence.VineEstS2
