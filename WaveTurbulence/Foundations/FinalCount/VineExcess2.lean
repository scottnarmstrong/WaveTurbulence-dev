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

end WaveTurbulence.FinalCount
