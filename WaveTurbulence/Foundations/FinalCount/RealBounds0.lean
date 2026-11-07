/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaDev
/-! Real-analysis lemmas for the simplification of the `α`-cut deviation (FINALCOUNT-G2 step 4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- `(log L)^4 ≤ (8/ε)^4 L^{ε}`-type bound: a power of the logarithm is dominated by any power of `L`. -/
theorem log_pow_four_le (L ε : ℝ) (hL : 1 ≤ L) (hε : 0 < ε) :
    Real.log L ^ 4 ≤ (4 / ε) ^ 4 * L ^ ε := by
  have h0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have h1 : Real.log L ≤ L ^ (ε / 4) / (ε / 4) :=
    Real.log_le_rpow_div (by linarith) (by positivity)
  have h2 : Real.log L ^ 4 ≤ (L ^ (ε / 4) / (ε / 4)) ^ 4 := pow_le_pow_left₀ h0 h1 4
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, ← Real.rpow_natCast (L ^ (ε / 4)) 4, ← Real.rpow_mul (by linarith)]
  have : ε / 4 * ((4 : ℕ) : ℝ) = ε := by push_cast; ring
  rw [this]
  have : (ε / 4) ^ 4 = (4 / ε)⁻¹ ^ 4 := by rw [inv_div]
  rw [this, inv_pow]; field_simp


/-- The normalisation factor of the `α`-cut, bounded by `L^{-(d-γ)} (log L)^4`. -/
theorem c0_le (d : ℕ) {L γ δ C₁ : ℝ} (hL : 1 ≤ L) (hδ0 : 0 < δ) (hδ : δ ≤ 1) (hC : 1 ≤ C₁) :
    L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4 ≤ L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4 := by
  have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ0.le hδ (by norm_num)
  have h3 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ0.le _
  have h4 : C₁⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by nlinarith [inv_nonneg.2 (zero_le_one.trans hC)]
  have h5 : 0 ≤ L ^ (-((d : ℝ) - γ)) * Real.log L ^ 4 :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
  nlinarith

theorem rpow_nat_mul_neg (d : ℕ) {L γ : ℝ} (hL : 0 < L) :
    L ^ d * L ^ (-((d : ℝ) - γ)) = L ^ γ := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hL]; congr 1; ring

end WaveTurbulence.FinalCount
