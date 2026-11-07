/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExponentialBoxFourier
import Mathlib.Tactic

/-!
# Pointwise agreement of the exponential extension kernel

Multiplying by the reciprocal exponential exactly recovers the literal
closed-interval and strict-half-line indicators. This is a pointwise
identity, as required by the restriction norm.
-/

@[expose] public section
set_option autoImplicit false

open Set

namespace WaveTurbulence.SumintPar

/-- The factored kernel is the exponential times the exact rectangular indicator. -/
theorem exponentialBox_eq_ite (a b u : ℝ) (z : Fin 3 → ℝ) :
    exponentialBox a b u z =
      if z 0 ∈ Icc a b ∧ z 1 < u ∧ z 2 < u then
        (Real.exp (-z 0+z 1+z 2) : ℂ) else 0 := by
  classical
  unfold exponentialBox
  rw [Fin.prod_univ_three]
  change exponentialInterval (Icc a b) (-1) (z 0) *
    exponentialInterval (Iio u) 1 (z 1) * exponentialInterval (Iio u) 1 (z 2) = _
  by_cases h₀ : z 0 ∈ Icc a b <;> by_cases h₁ : z 1 < u <;> by_cases h₂ : z 2 < u
  all_goals simp [exponentialInterval, h₀, h₁, h₂, Real.exp_add, Complex.ofReal_mul]

/-- The smooth inverse exponential gives exactly one on the source rectangular domain and zero elsewhere. -/
theorem exponentialBox_inverse_weight (a b u : ℝ) (z : Fin 3 → ℝ) :
    (Real.exp (z 0-z 1-z 2) : ℂ) * exponentialBox a b u z =
      if z 0 ∈ Icc a b ∧ z 1 < u ∧ z 2 < u then (1 : ℂ) else 0 := by
  classical
  rw [exponentialBox_eq_ite]
  by_cases h : z 0 ∈ Icc a b ∧ z 1 < u ∧ z 2 < u
  · rw [ite_eq_left h, ite_eq_left h, ← Complex.ofReal_mul, ← Real.exp_add]
    have he : (z 0-z 1-z 2)+(-z 0+z 1+z 2) = 0 := by ring
    rw [he, Real.exp_zero, Complex.ofReal_one]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

end WaveTurbulence.SumintPar
