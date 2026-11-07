/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInverseMatrixApply
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Both exact inverse identities for the full-chain source pair matrix -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem assemblyInversePairMatrix_mul (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    assemblyInversePairMatrix hM9 B hG * assemblyPairMatrix hM9 B hG = 1 := by
  classical
  ext v j
  let x : (assemblyShape hM9 B).VIdx → (Fin 1 → ℤ) := fun u _ => if u = j then 1 else 0
  have he := congrArg (fun f : Fin 1 → ℤ => f 0) (assemblyInversePairMatrix_apply hM9 B hG x v)
  have hsum (f : (assemblyShape hM9 B).VIdx → ℤ) :
      ((∑ u, f u • x u) : Fin 1 → ℤ) 0 = f j := by
    simp [x,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  have hv : x v 0 = if v = j then 1 else 0 := rfl
  simpa only [Matrix.mul_apply,Matrix.one_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hsum,hv] using he.symm

/-- Square integer matrices are directly finite. This obtains the other
inverse identity without a determinant assumption or a separate bijection. -/
theorem assemblyPairMatrix_mul_inverse (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain) :
    assemblyPairMatrix hM9 B hG * assemblyInversePairMatrix hM9 B hG = 1 :=
  mul_eq_one_comm.mp (assemblyInversePairMatrix_mul hM9 B hG)

end WaveTurbulence.VineEstS2
