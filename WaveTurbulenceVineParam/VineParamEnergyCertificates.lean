/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamQuadraticMatrices
import Mathlib.Tactic

/-! # Source energy rows and their dimension-independent coefficient certificates

A directed bond contributes minus its squared momentum at its tail and plus
at its head, so these are the negative molecular Gamma factors. Coefficient
identities are checked over integers before evaluation on real momenta.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset Matrix
variable {ι β V E : Type*} [Fintype ι] [Fintype β] [DecidableEq V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integer incidence sign for the negative molecular Gamma convention. -/
@[expose] def energySign (ends : β → V×V) (v : V) (j : β) : ℤ :=
  (if (ends j).2=v then 1 else 0)-(if (ends j).1=v then 1 else 0)

/-- Negative molecular Gamma, expressed by one label for each directed bond. -/
@[expose] def directedEnergy (ends : β → V×V) (v : V) (k : β → E) : ℝ :=
  ∑ j,(energySign ends v j : ℝ)*‖k j‖^2

/-- The exact integer coefficient matrix of one reconstructed atom resonance. -/
@[expose] def energyMatrix (ends : β → V×V) (v : V) (A : Matrix β ι ℤ) : Matrix ι ι ℤ :=
  fun i l => ∑ j,energySign ends v j*A j i*A j l

/-- Evaluation commutes with a finite sum of coefficient matrices. -/
theorem quadraticEval_sum (Qs : β → Matrix ι ι ℤ) (x : ι → E) :
    quadraticEval (∑ j,Qs j) x=∑ j,quadraticEval (Qs j) x := by
  simp only [quadraticEval,Matrix.sum_apply,Int.cast_sum,sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- An integer multiple of an outer product evaluates to the expected norm. -/
theorem quadraticEval_scaled_square (s : ℤ) (a : ι → ℤ) (x : ι → E) :
    quadraticEval (fun i l => s*a i*a l) x=(s : ℝ)*‖∑ i,a i • x i‖^2 := by
  rw [← quadraticEval_square]
  simp only [quadraticEval,intOuter,Int.cast_mul,mul_assoc]
  simp only [Finset.mul_sum]

/-- Every certified integer energy matrix gives the exact source resonance
for the actual vector-valued momenta reconstructed by its label rows. -/
theorem energyMatrix_eval (ends : β → V×V) (v : V) (A : Matrix β ι ℤ) (x : ι → E) :
    quadraticEval (energyMatrix ends v A) x=directedEnergy ends v (intEval A x) := by
  let Qs : β → Matrix ι ι ℤ := fun j => fun i l => energySign ends v j*A j i*A j l
  have he : energyMatrix ends v A=∑ j : β,Qs j := by
    ext i l
    exact (Matrix.sum_apply i l univ Qs).symm
  rw [he,quadraticEval_sum Qs x]
  simp only [Qs,quadraticEval_scaled_square,directedEnergy,intEval]

end WaveTurbulence.Vine.Param
