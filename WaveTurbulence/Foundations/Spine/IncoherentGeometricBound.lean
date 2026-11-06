/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.PositiveGeometricSum
/-! Explicit evaluation of the count-weighted incoherency sum in TARGET L2230–2232. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

theorem counted_incoherent_sum_le {L a C₁ δ : ℝ} (hL : 0 ≤ L)
    (hC₁ : 0 ≤ C₁) (hδ : 0 ≤ δ) (p n : ℕ)
    (hr : (2 : ℝ) ^ (9 * p) * L ^ (-a) ≤ 1 / 2) :
    (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
      (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
        (C₁ * (C₁ * δ) ^ n * L ^ (-a * g))) ≤
      2 * C₁ * ((12 ^ 9 : ℝ) * 4 * C₁ * δ) ^ n * (2 : ℝ) ^ (9 * p) * L ^ (-a) := by
  have he : ∀ g : ℕ,
      (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
        (C₁ * (C₁ * δ) ^ n * L ^ (-a * g)) =
      (C₁ * ((12 ^ 9 : ℝ) * 4 * C₁ * δ) ^ n) *
        ((2 : ℝ) ^ (9 * p) * L ^ (-a)) ^ g := by
    intro g
    push_cast
    rw [Real.rpow_mul hL, Real.rpow_natCast]
    rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
    simp only [mul_pow]
    ring
  simp_rw [he]
  rw [← mul_sum]
  have h0 : 0 ≤ (2 : ℝ) ^ (9 * p) * L ^ (-a) := mul_nonneg (by positivity) (Real.rpow_nonneg hL _)
  have houter : 0 ≤ C₁ * ((12 ^ 9 : ℝ) * 4 * C₁ * δ) ^ n := by positivity
  have h := mul_le_mul_of_nonneg_left (sum_positive_powers_le h0 hr n) houter
  exact h.trans_eq (by ring)

end WaveTurbulence.LGSpine
