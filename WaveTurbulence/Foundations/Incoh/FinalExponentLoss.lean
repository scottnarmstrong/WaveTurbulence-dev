/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# The final small-eta exponent loss in Proposition 5.1

The analytic core loses `100d eta`; the standing smallness condition
absorbs this into the source proposition's printed square-root loss.
-/

public section

namespace WaveTurbulence.Incoh

/-- A linear eta loss is bounded by its square root at the literal quadratic smallness scale. -/
theorem linear_eta_loss_le_sqrt {A η : ℝ} (_hA : 0 ≤ A) (hη : 0 ≤ η) (hsmall : A ^ 2 * η ≤ 1) :
    A * η ≤ Real.sqrt η := by
  have hs : (A * η) ^ 2 ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hη]
  nlinarith [Real.sqrt_nonneg η, Real.sq_sqrt hη]

/-- The actual `100d eta` core loss implies the printed square-root incoherence exponent. -/
theorem incoherence_rpow_le_sqrt_loss {d g : ℕ} {L η γ₁ : ℝ}
    (hL : 1 ≤ L) (hη : 0 ≤ η) (hsmall : (100 * (d : ℝ)) ^ 2 * η ≤ 1) :
    L ^ (-(γ₁ - 100 * (d : ℝ) * η) * g) ≤ L ^ (-(γ₁ - Real.sqrt η) * g) := by
  have hloss := linear_eta_loss_le_sqrt (by positivity : 0 ≤ 100 * (d : ℝ)) hη hsmall
  apply Real.rpow_le_rpow_of_exponent_le hL
  exact mul_le_mul_of_nonneg_right (neg_le_neg (sub_le_sub_left hloss γ₁)) (Nat.cast_nonneg g)

end WaveTurbulence.Incoh
