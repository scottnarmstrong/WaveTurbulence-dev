/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Prof2
/-! # FL-FAM: the numerical absorption step. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Fam

theorem numeric_absorb {L δ ν lo K Bexp e : ℝ} {N : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ) (hlo : 0 < lo)
    (hK0 : 0 ≤ K) (hsmall : 6 * lo * δ ^ (2 * ν) ≤ 1) (hK : K ≤ L ^ e) :
    K * (L ^ Bexp * δ ^ (6 * ν * N) * (2 * lo) ^ N * 3 ^ N) ≤ L ^ (Bexp + e) * δ ^ (4 * ν * N) := by
  have hL0 : 0 < L := by linarith
  have h6 : δ ^ (6 * ν * N) = δ ^ (4 * ν * N) * (δ ^ (2 * ν)) ^ N := by
    rw [show 6 * ν * (N : ℝ) = 4 * ν * N + (2 * ν) * N by ring, Real.rpow_add hδ,
      Real.rpow_mul_natCast hδ.le (2 * ν) N]
  have h1 : (2 * lo) ^ N * 3 ^ N * (δ ^ (2 * ν)) ^ N ≤ 1 := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_one₀ (by positivity) ?_
    nlinarith
  have hA : 0 ≤ L ^ Bexp * δ ^ (4 * ν * N) := by positivity
  calc K * (L ^ Bexp * δ ^ (6 * ν * N) * (2 * lo) ^ N * 3 ^ N)
      = K * (L ^ Bexp * δ ^ (4 * ν * N)) * ((2 * lo) ^ N * 3 ^ N * (δ ^ (2 * ν)) ^ N) := by
        rw [h6]; ring
    _ ≤ K * (L ^ Bexp * δ ^ (4 * ν * N)) * 1 := by
        gcongr
    _ ≤ L ^ e * (L ^ Bexp * δ ^ (4 * ν * N)) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hK hA
    _ = L ^ (Bexp + e) * δ ^ (4 * ν * N) := by
        rw [Real.rpow_add hL0]; ring

end WaveTurbulence.Flower.Fam
