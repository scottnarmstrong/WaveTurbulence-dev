/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.ProdDyadicCut
public import WaveTurbulence.Foundations.FC23.FrozenRadialBridge
/-! The exact per-tree T1/T2 decomposition and auxiliary leaf cutoff.
The leaf carrier here includes both signs; positive input representatives alone
are not sufficient for the conservation argument. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Finset Polynomial
variable {ι : Type*}

def affineProduct (s : Finset ι) (g h : ι → ℂ) : ℂ[X] :=
  ∏ a ∈ s, (C (g a) + X * C (h a))

theorem affineProduct_eval (s : Finset ι) (g h : ι → ℂ) (z : ℂ) :
    (affineProduct s g h).eval z = ∏ a ∈ s, (g a + z * h a) := by
  simp only [affineProduct, eval_prod, eval_add, eval_C, eval_mul, eval_X]

theorem affineProduct_natDegree (s : Finset ι) (g h : ι → ℂ) :
    (affineProduct s g h).natDegree ≤ s.card := by
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ a ∈ s, (C (g a) + X * C (h a)).natDegree) ≤ ∑ _a ∈ s, 1 := by
      apply sum_le_sum
      intro a _
      apply natDegree_add_le_of_degree_le
      · simp only [natDegree_C]; omega
      · exact (natDegree_mul_le).trans (by simp only [natDegree_X, natDegree_C]; omega)
    _ = s.card := by simp only [sum_const, smul_eq_mul, mul_one]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end WaveTurbulence.FC23
