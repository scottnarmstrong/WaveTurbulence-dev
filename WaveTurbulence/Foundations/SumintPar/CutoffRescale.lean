/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputCutoffInsertion
public import WaveTurbulence.Foundations.LemLin.LinearSum
import Mathlib.Tactic

/-!
# Exact width-four cutoff rescaling

The integer summation variables are unchanged. The mesh parameter becomes
`4L`, the cutoff centre is divided by four and linear frequencies are
multiplied by four. These are identities, with no asymptotic constants.
-/

@[expose] public section
set_option autoImplicit false

open WithLp
open scoped InnerProductSpace

namespace WaveTurbulence.SumintPar

/-- Scaling the mesh is the same as scaling the Euclidean lattice vector. -/
theorem latticePoint_four_mul {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePoint L n = (4 : ℝ) • latticePoint (4*L) n := by
  ext j
  change (n j : ℝ)/L = 4*((n j : ℝ)/(4*L))
  by_cases hL : L = 0
  · simp [hL]
  · field_simp

/-- The source inserted cutoff is exactly the landed width-one cutoff at mesh `4L`. -/
theorem inputCutoff_rescale {d : ℕ} (L : ℝ) (a : Fin d → ℝ) (n : Fin d → ℤ) :
    (inputCutoff a (latticePoint L n) : ℂ) =
      Fourier.chi0TensorComplex (ofLp (latticePoint (4*L) n - (1/4:ℝ) • toLp 2 a)) := by
  unfold inputCutoff Fourier.chi0TensorComplex
  congr 2
  funext j
  change ((n j : ℝ)/L-a j)/4 = (n j : ℝ)/(4*L)-(1/4)*a j
  by_cases hL : L = 0
  · simp [hL]; ring
  · field_simp

/-- Exact conversion of the inserted linear lattice sum to the landed one. -/
theorem inputCutoff_linear_sum_eq {d : ℕ} (L : ℝ) (a : Fin d → ℝ) (w : Mom d) :
    (∑' n : Fin d → ℤ, (inputCutoff a (latticePoint L n) : ℂ) *
      (Real.fourierChar (inner ℝ w (latticePoint L n)) : ℂ)) =
        LemLin.linearLatticeSum (4*L) ((1/4:ℝ) • toLp 2 a) ((4:ℝ) • w) := by
  unfold LemLin.linearLatticeSum
  apply tsum_congr
  intro n
  rw [inputCutoff_rescale]
  congr 2
  rw [latticePoint_four_mul L n, inner_smul_right, inner_smul_left]
  simp only [conj_trivial]
  rfl

end WaveTurbulence.SumintPar
