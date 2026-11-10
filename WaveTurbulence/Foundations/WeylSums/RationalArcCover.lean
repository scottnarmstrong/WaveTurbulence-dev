/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import WaveTurbulence.Foundations.WeylSums.ArcProfile
import Mathlib.Tactic

/-!
# Rational covers of a unit interval

Dirichlet approximation selects one term of a finite positive major-arc
envelope. Integrating this envelope separates arc mass from denominator
counting. The slight enlargement `-1 ≤ a ≤ q+1` avoids endpoint conventions.
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- Positive envelope formed from all candidate rational arcs. -/
@[expose] noncomputable def rationalArcEnvelope (L σ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 N, (q : ℝ) ^ (-σ) *
    ∑ a ∈ Icc (-1 : ℤ) ((q : ℤ) + 1), scaledArcProfile L σ ((a : ℝ) / q) t

theorem rationalArcEnvelope_nonneg (L σ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ rationalArcEnvelope L σ N t := by
  apply sum_nonneg
  intro q _
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sum_nonneg (fun a _ => scaledArcProfile_nonneg _ _ _ _))

theorem numerator_range_card (q : ℕ) : (Icc (-1 : ℤ) ((q : ℤ) + 1)).card = q + 3 := by
  rw [Int.card_Icc]
  omega

end WaveTurbulence.WeylSums
