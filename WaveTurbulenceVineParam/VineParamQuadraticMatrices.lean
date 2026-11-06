/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamIntegerMatrices
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Integer quadratic certificates evaluate to exact resonance identities -/

public section
namespace WaveTurbulence.Vine.Param
open Finset Matrix
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The integer outer product, whose quadratic evaluation is an inner product. -/
@[expose] def intOuter (a b : ι → ℤ) : Matrix ι ι ℤ := fun i j => a i*b j

/-- Exact quadratic evaluation on vector-valued momentum coordinates. -/
@[expose] def quadraticEval (Q : Matrix ι ι ℤ) (x : ι → E) : ℝ :=
  ∑ i,∑ j,(Q i j : ℝ)*inner ℝ (x i) (x j)

/-- Outer-product identities over integers hold in every real momentum dimension. -/
theorem quadraticEval_outer (a b : ι → ℤ) (x : ι → E) :
    quadraticEval (intOuter a b) x=
      inner ℝ (∑ i,a i • x i) (∑ j,b j • x j) := by
  simp only [quadraticEval,intOuter,Int.cast_mul,sum_inner,inner_sum,
    ← Int.cast_smul_eq_zsmul ℝ,real_inner_smul_left,real_inner_smul_right,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Quadratic certificates respect addition. -/
theorem quadraticEval_add (A B : Matrix ι ι ℤ) (x : ι → E) :
    quadraticEval (A+B) x=quadraticEval A x+quadraticEval B x := by
  simp only [quadraticEval,Matrix.add_apply,Int.cast_add,add_mul,sum_add_distrib]

/-- Quadratic certificates respect negation. -/
theorem quadraticEval_neg (A : Matrix ι ι ℤ) (x : ι → E) :
    quadraticEval (-A) x= -quadraticEval A x := by
  simp only [quadraticEval,Matrix.neg_apply,Int.cast_neg,neg_mul,sum_neg_distrib]

/-- A squared norm is the diagonal outer-product certificate. -/
theorem quadraticEval_square (a : ι → ℤ) (x : ι → E) :
    quadraticEval (intOuter a a) x=‖∑ i,a i • x i‖^2 := by
  rw [quadraticEval_outer,real_inner_self_eq_norm_sq]

end WaveTurbulence.Vine.Param
