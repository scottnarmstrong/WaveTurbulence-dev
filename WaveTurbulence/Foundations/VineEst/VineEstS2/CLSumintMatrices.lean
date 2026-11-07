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

/-! # Literal source pair and branch decoder matrices on sumint rows -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyPairMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  fun v j => chainDecodeFree hM9 B (clOrderedPairBond B.isBlock R hG (assemblyPairOrder hG B hM9) ((assemblyRowEquiv hM9 B).symm v))
    ((assemblyVectorEquiv hM9 B).symm j)

noncomputable def assemblyBranchMatrix (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    Matrix (assemblyShape hM9 B).VIdx (assemblyShape hM9 B).VIdx ℤ :=
  fun v j => chainDecodeFree hM9 B (clOrderedBranchBond B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v))
    ((assemblyVectorEquiv hM9 B).symm j)

theorem assemblyPairMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v j : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (assemblyPairMatrix hM9 B hG v j) :=
  chainDecodeFree_unit hM9 B _ _

theorem assemblyBranchMatrix_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v j : (assemblyShape hM9 B).VIdx) : IsUnitCoeff (assemblyBranchMatrix hM9 B v j) :=
  chainDecodeFree_unit hM9 B _ _

/-- The affine term g+q(g-h) has the exact common-coset normalization. -/
def gapBoundaryRow (q : ℤ) (c : Fin 4) : ℤ := if c = 2 then 1+q else if c = 3 then -q else 0

theorem sum_gapBoundaryRow (q : ℤ) : ∑ c, gapBoundaryRow q c = 1 := by
  simp only [Fin.sum_univ_succ,gapBoundaryRow]
  norm_num

end WaveTurbulence.VineEstS2
