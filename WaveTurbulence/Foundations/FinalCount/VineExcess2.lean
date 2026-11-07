/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess
public import WaveTurbulence.Foundations.FinalCount.VineDev
public import WaveTurbulence.Foundations.FinalCount.TriArith2
/-! Vine removal, part 9 (FINALCOUNT-G2): the cancellation `𝔉 · L^{-m(d-γ)} (C₁⁻¹δ^{1/2})^m = C₁^{-m} ρ^d L^{2γ} (log L)^e`
(L1799--L1801). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

theorem delta_qq_pow {δ C₁ : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C₁) (m : ℕ) :
    δ ^ (-(m : ℝ) / 2) * qq δ C₁ ^ m ≤ 1 := by
  unfold qq
  have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have h0 : 0 ≤ C₁⁻¹ := inv_nonneg.2 (zero_le_one.trans hC)
  have e : (δ ^ (1 / 2 : ℝ)) ^ m = δ ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; ring
  have e2 : δ ^ (-(m : ℝ) / 2) * δ ^ ((m : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hδ, show -(m : ℝ) / 2 + (m : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  rw [mul_pow, e]
  calc δ ^ (-(m : ℝ) / 2) * (C₁⁻¹ ^ m * δ ^ ((m : ℝ) / 2)) = C₁⁻¹ ^ m * (δ ^ (-(m : ℝ) / 2) * δ ^ ((m : ℝ) / 2)) := by ring
    _ ≤ 1 := by rw [e2, mul_one]; exact pow_le_one₀ h0 h1

theorem L_cancel (d m : ℕ) {L γ ρ : ℝ} (hL : 0 < L) :
    L ^ d * (ρ * L) ^ d * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * (L ^ (-((d : ℝ) - γ))) ^ m = ρ ^ d * L ^ (2 * γ) := by
  have e1 : (L ^ (-((d : ℝ) - γ))) ^ m = L ^ (-((d : ℝ) - γ) * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  have e2 : L ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
  have e3 : L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * m) = L ^ (-2 * ((d : ℝ) - γ)) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  have e4 : L ^ (d : ℝ) * L ^ (d : ℝ) * L ^ (-2 * ((d : ℝ) - γ)) = L ^ (2 * γ) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]; congr 1; ring
  calc L ^ d * (ρ * L) ^ d * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * (L ^ (-((d : ℝ) - γ))) ^ m
      = ρ ^ d * (L ^ d * L ^ d * (L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * m))) := by
        rw [e1, mul_pow]; ring
    _ = ρ ^ d * L ^ (2 * γ) := by rw [e3, e2, e4]

/-- The real inequality behind `vine_excess_single`. -/
theorem vine_real (d m e : ℕ) {L γ δ C₁ ρ Cf Λ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hρ0 : 0 ≤ ρ)
    (hCf : 0 ≤ Cf) (hΛ : 0 < Λ) (hlog : 1 ≤ Real.log L) :
    ((⌊vineF d L γ δ ρ Cf Λ m e⌋₊ : ℕ) : ℝ) * ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8 * Λ) ≤
      Cf * (ρ ^ d * L ^ (2 * γ) * Real.log L ^ (e + 8)) := by
  have hL0 : 0 < L := by linarith
  have hq := qq_nonneg hδ.le (zero_le_one.trans hC)
  have hF0 : 0 ≤ vineF d L γ δ ρ Cf Λ m e := by
    unfold vineF
    have : 0 ≤ Real.log L := by linarith
    positivity
  have hN : ((⌊vineF d L γ δ ρ Cf Λ m e⌋₊ : ℕ) : ℝ) ≤ vineF d L γ δ ρ Cf Λ m e := Nat.floor_le hF0
  have hrf : 0 ≤ (L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8 := by
    have : 0 ≤ Real.log L := by linarith
    positivity
  have hB0 : vineF d L γ δ ρ Cf Λ m e * Λ =
      Cf * L ^ d * (ρ * L) ^ d * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) * δ ^ (-(m : ℝ) / 2) * Real.log L ^ e := by
    unfold vineF; field_simp
  have hcancel := L_cancel d m (L := L) (γ := γ) (ρ := ρ) hL0
  have hdq := delta_qq_pow hδ hC m
  calc ((⌊vineF d L γ δ ρ Cf Λ m e⌋₊ : ℕ) : ℝ) * ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8 * Λ)
      = (((⌊vineF d L γ δ ρ Cf Λ m e⌋₊ : ℕ) : ℝ) * Λ) * ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8) := by ring
    _ ≤ (vineF d L γ δ ρ Cf Λ m e * Λ) * ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8) := by
        gcongr
    _ = Cf * Real.log L ^ (e + 8) * (L ^ d * (ρ * L) ^ d * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) *
          (L ^ (-((d : ℝ) - γ))) ^ m) * (δ ^ (-(m : ℝ) / 2) * qq δ C₁ ^ m) := by
        rw [hB0]; ring
    _ ≤ Cf * Real.log L ^ (e + 8) * (ρ ^ d * L ^ (2 * γ)) * 1 := by
        rw [hcancel]
        have : 0 ≤ Cf * Real.log L ^ (e + 8) * (ρ ^ d * L ^ (2 * γ)) := by
          have : 0 ≤ Real.log L := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left hdq this |>.trans_eq' (by ring) |>.trans (by ring_nf; exact le_rfl)
    _ = Cf * (ρ ^ d * L ^ (2 * γ) * Real.log L ^ (e + 8)) := by ring

end WaveTurbulence.FinalCount
