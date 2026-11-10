/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Orthogonality for Hua's moments

DH21 Lemma A.5 reduces even moments of quadratic exponential sums to counting
integer resonances. This file supplies the finite Fourier orthogonality step.
-/

public section

open MeasureTheory Finset
open scoped BigOperators ComplexConjugate

namespace WaveTurbulence.WeylSums

/-- The additive exponential takes finite sums to finite products. -/
theorem e_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ S, f i) = ∏ i ∈ S, e (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [sum_empty, e_zero, prod_empty]
  | @insert a S ha ih => rw [sum_insert ha, prod_insert ha, e_add, ih]

theorem conj_e (t : ℝ) : conj (e t) = e (-t) := by
  rw [show -t = 0 - t by ring, e_sub, e_zero, one_div, Complex.inv_eq_conj (norm_e t)]

end WaveTurbulence.WeylSums
