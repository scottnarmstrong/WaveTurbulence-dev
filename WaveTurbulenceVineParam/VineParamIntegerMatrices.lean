/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic

/-! # Integer coefficient certificates act on arbitrary momentum groups

Explicit matrix identities over integers certify the coordinate changes.
The same certificate acts on the integer lattice and on real momenta, with
no determinant or measure factor hidden in the transport.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset Matrix
variable {ι κ ν E : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [AddCommGroup E]

/-- Evaluation of a matrix of integer coefficients on a momentum vector. -/
@[expose] def intEval (A : Matrix ι κ ℤ) (x : κ → E) : ι → E :=
  fun i => ∑ j,A i j • x j

omit [Fintype ι] in
/-- Composition of integer certificates is composition on actual momenta. -/
theorem intEval_mul (A : Matrix ι κ ℤ) (B : Matrix κ ν ℤ) (x : ν → E) :
    intEval (A*B) x=intEval A (intEval B x) := by
  funext i
  simp only [intEval,Matrix.mul_apply,sum_smul,smul_sum,mul_zsmul]
  exact Finset.sum_comm

/-- The identity certificate fixes all coordinates. -/
theorem intEval_one [DecidableEq ι] (x : ι → E) : intEval (1 : Matrix ι ι ℤ) x=x := by
  funext i
  simp only [intEval,Matrix.one_apply,ite_smul,one_zsmul,zero_zsmul,sum_ite_eq,mem_univ,ite_true]

/-- Two explicit inverse integer matrices give a genuine equivalence on
any additive group; this is the algebraic meaning of unimodularity here. -/
@[expose] def integerMatrixEquiv [DecidableEq ι] (A B : Matrix ι ι ℤ)
    (hAB : A*B=1) (hBA : B*A=1) : (ι → E) ≃ (ι → E) where
  toFun := intEval A
  invFun := intEval B
  left_inv := by intro x; rw [← intEval_mul,hBA,intEval_one]
  right_inv := by intro x; rw [← intEval_mul,hAB,intEval_one]

end WaveTurbulence.Vine.Param
