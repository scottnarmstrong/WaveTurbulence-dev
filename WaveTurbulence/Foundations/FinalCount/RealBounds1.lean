/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RealBounds0
/-! Real bounds for the `α`-cut with `κ = 0` (FINALCOUNT-G2 step 4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- Common reduction: the `α`-cut deviation is at most `2 A^d (8 R L^{2γ} + 5) L^{γ-d} (log L)^4`-shaped. -/
theorem alphaDev_reduce (d : ℕ) {L γ δ C₁ R ρ : ℝ} (hL : 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) :
    (alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R ρ : ℝ) *
        (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4) ≤
      (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) * (L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4) := by
  have hL0 : 0 < L := by linarith
  have hτ : 0 < δ⁻¹ * L ^ (-2 * γ) := by positivity
  have h1 := alphaN'_le (d := d) L _ R ρ hL0 hτ hR hρ
  have h2 : 8 * R / (δ⁻¹ * L ^ (-2 * γ)) = 8 * δ * R * L ^ (2 * γ) := by
    have : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    have h' : L ^ (-2 * γ) = (L ^ (2 * γ))⁻¹ := by rw [neg_mul, Real.rpow_neg hL0.le]
    rw [h']; field_simp
  rw [h2] at h1
  have h3 : 8 * δ * R * L ^ (2 * γ) ≤ 8 * R * L ^ (2 * γ) := by
    have : 0 ≤ R * L ^ (2 * γ) := mul_nonneg hR (Real.rpow_nonneg hL0.le _)
    nlinarith
  have h4 := c0_le d (γ := γ) hL hδ0 hδ hC
  have hA : 0 ≤ (2 * ρ * L + 1) ^ d := by positivity
  have h5 : (alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R ρ : ℝ) ≤
      (2 * ρ * L + 1) ^ d * (2 * (8 * R * L ^ (2 * γ) + 5)) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have hnn : 0 ≤ L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4 := by
    have : 0 ≤ C₁⁻¹ * δ ^ (1 / 2 : ℝ) := mul_nonneg (inv_nonneg.2 (by linarith)) (Real.rpow_nonneg hδ0.le _)
    have := Real.log_nonneg hL
    positivity
  exact mul_le_mul h5 h4 hnn (by positivity)

end WaveTurbulence.FinalCount
