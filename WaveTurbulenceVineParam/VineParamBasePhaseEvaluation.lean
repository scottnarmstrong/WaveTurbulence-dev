/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamEnergyCertificates
import Mathlib.Tactic

/-! # Dimension-independent evaluation of the signed base-vine phase certificates -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The standard integer row selecting one actual free coordinate. -/
@[expose] def coordinateRow (i : ι) : ι → ℤ := fun j => if j=i then 1 else 0

omit [InnerProductSpace ℝ E] in
/-- Evaluation of a standard integral coordinate row is exact. -/
theorem coordinateRow_eval (i : ι) (x : ι → E) :
    (∑ j,coordinateRow i j • x j)=x i := by simp [coordinateRow]

omit [InnerProductSpace ℝ E] in
/-- The nonlinear core argument is the exact signed coordinate sum. -/
theorem coordinateRow_core_eval (i j k : ι) (x : ι → E) :
    (∑ l,(coordinateRow i l+coordinateRow j l-coordinateRow k l) • x l)=x i+x j-x k := by
  simp only [sub_smul,add_smul,sum_sub_distrib,sum_add_distrib,coordinateRow_eval]

omit [DecidableEq ι] in
/-- Integer-scaled matrix certificates evaluate with their actual scalar sign. -/
theorem quadraticEval_intScale (s : ℤ) (Q : Matrix ι ι ℤ) (x : ι → E) :
    quadraticEval (fun i j => s*Q i j) x=(s : ℝ)*quadraticEval Q x := by
  simp only [quadraticEval,Int.cast_mul,mul_assoc,Finset.mul_sum]

omit [DecidableEq ι] in
/-- A signed symmetric outer-product certificate gives its exact bilinear
phase over every real momentum space. -/
theorem quadraticEval_signed_symmetric (s : ℤ) (a b : ι → ℤ) (x : ι → E) :
    quadraticEval (fun i j => s*((intOuter a b+intOuter b a) i j)) x=
      2*(s : ℝ)*inner ℝ (∑ i,a i • x i) (∑ i,b i • x i) := by
  rw [quadraticEval_intScale,quadraticEval_add,quadraticEval_outer,quadraticEval_outer]
  rw [real_inner_comm (∑ i,b i • x i) (∑ i,a i • x i)]
  ring

omit [DecidableEq ι] in
/-- An unscaled symmetric integer certificate evaluates exactly. -/
theorem quadraticEval_symmetric (a b : ι → ℤ) (x : ι → E) :
    quadraticEval (intOuter a b+intOuter b a) x=
      2*inner ℝ (∑ i,a i • x i) (∑ i,b i • x i) := by
  rw [quadraticEval_add,quadraticEval_outer,quadraticEval_outer,
    real_inner_comm (∑ i,b i • x i) (∑ i,a i • x i)]
  ring

/-- The first signed core/rung factor from an exact integer certificate. -/
theorem quadraticEval_signed_coordinates (s : ℤ) (i j : ι) (x : ι → E) :
    quadraticEval (fun a b => s*((intOuter (coordinateRow i) (coordinateRow j)+
      intOuter (coordinateRow j) (coordinateRow i)) a b)) x=2*(s : ℝ)*inner ℝ (x i) (x j) := by
  rw [quadraticEval_signed_symmetric,coordinateRow_eval,coordinateRow_eval]

/-- The F79 nonlinear signed core form follows directly from its checked
integer matrix identity, without a dimension-specific argument. -/
theorem quadraticEval_signed_nonlinear_core (s : ℤ) (i j k : ι) (x : ι → E) :
    quadraticEval (fun a b => s*((intOuter (coordinateRow k)
      (fun l => coordinateRow i l+coordinateRow j l-coordinateRow k l)+
      intOuter (fun l => coordinateRow i l+coordinateRow j l-coordinateRow k l)
        (coordinateRow k)) a b)) x=
      2*(s : ℝ)*inner ℝ (x k) (x i+x j-x k) := by
  rw [quadraticEval_signed_symmetric,coordinateRow_eval,coordinateRow_core_eval]

end WaveTurbulence.Vine.Param
