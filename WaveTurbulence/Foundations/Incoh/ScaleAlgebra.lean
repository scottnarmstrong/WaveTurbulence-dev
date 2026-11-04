/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LinkExponents

/-!
# Factoring the kinetic-scale link bounds

TARGET (incohproof16): the common per-link scale is
`δ⁻¹ L^(2(d−γ))`. These identities track both frequency pieces before
absorbing any constants.
-/

public section

namespace WaveTurbulence.Incoh

/-- Exact common-scale factorization in the coherent case. -/
theorem coherent_scale_identity {L : ℝ} (hL : 0 < L) (δ γ C₀ C₁ a p η : ℝ) :
    (δ * L ^ (2 * γ))⁻¹ * (C₀ * L ^ a + C₁ * L ^ (a - p + η)) =
      δ⁻¹ * L ^ (a - 2 * γ) * (C₀ + C₁ * L ^ (-p + η)) := by
  rw [mul_add, inverse_scale_mul_rpow hL, inverse_scale_mul_rpow hL]
  rw [show (a - p + η) - 2 * γ = (a - 2 * γ) + (-p + η) by ring, Real.rpow_add hL]
  ring

/-- Exact common-scale factorization in the incoherent case. -/
theorem incoherent_scale_identity {L : ℝ} (hL : 0 < L) (δ γ C₀ C₁ a p η : ℝ) :
    ((δ * L ^ (2 * γ))⁻¹) ^ 2 * (C₀ * L ^ a) +
        (δ * L ^ (2 * γ))⁻¹ * (C₁ * L ^ (a - p + η)) =
      δ⁻¹ * L ^ (a - 2 * γ) * (C₀ * δ⁻¹ * L ^ (-2 * γ) + C₁ * L ^ (-p + η)) := by
  rw [inverse_scale_sq_mul_rpow hL, inverse_scale_mul_rpow hL]
  rw [show a - 4 * γ = (a - 2 * γ) + (-2 * γ) by ring, Real.rpow_add hL,
    show (a - p + η) - 2 * γ = (a - 2 * γ) + (-p + η) by ring, Real.rpow_add hL]
  ring

/-- Numerical gain comparison for the two incoherent contributions. -/
theorem incoherent_gain_le {d : ℕ} {L γ η A B : ℝ} (hL : 1 ≤ L)
    (hη : 0 ≤ η) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A * L ^ (-2 * γ) + B * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η) ≤
      (A + B) * L ^ (-(incoherenceExponent d γ - η)) := by
  have hs : -2 * γ ≤ -(incoherenceExponent d γ - η) := by
    linarith [incoherenceExponent_le_two_mul d γ]
  have hl : -(2 * ((d : ℝ) - 1) * (1 - γ)) + η ≤ -(incoherenceExponent d γ - η) := by
    linarith [incoherenceExponent_le_longGain d γ]
  calc
    _ ≤ A * L ^ (-(incoherenceExponent d γ - η)) + B * L ^ (-(incoherenceExponent d γ - η)) :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hs) hA)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hl) hB)
    _ = _ := by ring

end WaveTurbulence.Incoh
