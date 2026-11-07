/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorTerms
import Mathlib.Tactic

/-!
# Exact powers after the source mesh and time rescalings

The fixed width-four mesh and source half scale change constants but
retain the exact delta and L exponents. The real power identity also
covers the fractional multiplier in case (c).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Exact mesh/time rescaling at arbitrary real powers. -/
theorem source_scale_rpow {L k δ a : ℝ} (hL : 0 < L) (hk : 0 < k) (hδ : 0 < δ)
    (ha : 0 ≤ a) (γ q e : ℝ) :
    (k*sourceHalfScale L γ δ)^(-q)*(a*L)^e =
      (k/2)^(-q)*δ^(-q)*a^e*L^(e-2*γ*q) := by
  have hs : k*sourceHalfScale L γ δ = ((k/2)*δ)*L^(2*γ) := by
    unfold sourceHalfScale
    ring
  rw [hs,Real.mul_rpow (by positivity : 0 ≤ (k/2)*δ) (Real.rpow_nonneg hL.le _),
    Real.mul_rpow (by positivity : 0 ≤ k/2) hδ.le,Real.mul_rpow ha hL.le,
    ← Real.rpow_mul hL.le]
  have hp : L^(2*γ*(-q))*L^e = L^(e-2*γ*q) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = ((k/2)^(-q)*δ^(-q)*a^e)*(L^(2*γ*(-q))*L^e) := by ring
    _ = _ := by rw [hp]

/-- One reciprocal source time scale has the ordinary pair exponent. -/
theorem source_scale_inv_mul_nat_pow {L k δ a : ℝ} (hL : 0 < L) (hk : 0 < k)
    (hδ : 0 < δ) (ha : 0 ≤ a) (γ : ℝ) (n : ℕ) :
    (k*sourceHalfScale L γ δ)⁻¹*(a*L)^n =
      (k/2)⁻¹*δ⁻¹*a^n*L^((n:ℝ)-2*γ) := by
  have h := source_scale_rpow hL hk hδ ha γ 1 (n:ℝ)
  simpa only [Real.rpow_neg_one,Real.rpow_natCast,mul_one] using h

/-- Two reciprocal source time scales have the normal factor exponent. -/
theorem source_scale_inv_sq_mul_nat_pow {L k δ a : ℝ} (hL : 0 < L) (hk : 0 < k)
    (hδ : 0 < δ) (ha : 0 ≤ a) (γ : ℝ) (n : ℕ) :
    (k*sourceHalfScale L γ δ)⁻¹*(k*sourceHalfScale L γ δ)⁻¹*(a*L)^n =
      (k/2)^(-2:ℝ)*δ^(-2:ℝ)*a^n*L^((n:ℝ)-4*γ) := by
  have h := source_scale_rpow hL hk hδ ha γ 2 (n:ℝ)
  have hs : 0 ≤ k*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  rw [Real.rpow_neg hs,Real.rpow_two,pow_two,mul_inv_rev] at h
  simpa only [Real.rpow_natCast,show 2*γ*2 = 4*γ by ring] using h

/-- The reciprocal-square source scale at an arbitrary real mesh exponent. -/
theorem source_scale_inv_sq_mul_rpow {L k δ a : ℝ} (hL : 0 < L) (hk : 0 < k)
    (hδ : 0 < δ) (ha : 0 ≤ a) (γ e : ℝ) :
    (k*sourceHalfScale L γ δ)⁻¹*(k*sourceHalfScale L γ δ)⁻¹*(a*L)^e =
      (k/2)^(-2:ℝ)*δ^(-2:ℝ)*a^e*L^(e-4*γ) := by
  have h := source_scale_rpow hL hk hδ ha γ 2 e
  have hs : 0 ≤ k*sourceHalfScale L γ δ := by unfold sourceHalfScale; positivity
  rw [Real.rpow_neg hs,Real.rpow_two,pow_two,mul_inv_rev] at h
  simpa only [show 2*γ*2 = 4*γ by ring] using h

end WaveTurbulence.SumintPar
