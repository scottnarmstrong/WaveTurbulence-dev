/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Normalization of the regular-couple approximation

DH23 (KQZdef) to (KQZapprox): the order is2n, so the old prefactor
has exponent2n; the number-theory estimate has exponentn. Their product
is geometric in delta with no residual power of L.
-/

public section
namespace WaveTurbulence.RegAsymp

/-- Exact cancellation of the lattice scale and reciprocal delta. -/
theorem normalization_identity (n : ℕ) {X δ : ℝ} (hX : X ≠ 0) (hδ : δ ≠ 0) (C : ℝ) :
    (δ / (2 * X)) ^ (2 * n) * (C * X ^ 2 * δ⁻¹) ^ n = (C * δ / 4) ^ n := by
  rw [pow_mul,← mul_pow]
  congr 1
  field_simp
  ring

/-- The scale appearing in Prop6.4 is the square of L^(d-gamma). -/
theorem lattice_scale_square {L : ℝ} (hL : 0 < L) (d : ℕ) (γ : ℝ) :
    L ^ (2 * (d : ℝ) - 2 * γ) = (L ^ ((d : ℝ) - γ)) ^ 2 := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
  congr 1
  ring

/-- The normalized error has no positive power of L. -/
theorem normalized_scale (n d : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : δ ≠ 0) (C : ℝ) :
    (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (C * L ^ (2 * (d : ℝ) - 2 * γ) * δ⁻¹) ^ n = (C * δ / 4) ^ n := by
  rw [lattice_scale_square hL d γ]
  exact normalization_identity n (ne_of_gt (Real.rpow_pos_of_pos hL _)) hδ C

/-- A phase scaled by s changes the normalization by s^(-n).
For the physical energy Omega=2<x,y>, the value is s=2. -/
theorem scaled_normalization_identity (n : ℕ) {X δ s : ℝ}
    (hX : X ≠ 0) (hδ : δ ≠ 0) (hs : s ≠ 0) (C : ℝ) :
    (δ / (2 * X)) ^ (2 * n) * (C * X ^ 2 * (s * δ)⁻¹) ^ n =
      (C * δ / (4 * s)) ^ n := by
  rw [pow_mul,← mul_pow]
  congr 1
  field_simp
  ring

end WaveTurbulence.RegAsymp
