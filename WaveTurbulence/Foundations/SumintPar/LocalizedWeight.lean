/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.LocalizationProfile
public import WaveTurbulence.Foundations.SumintPar.DerivativeBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-!
# Localizing finite-regularity sumint weights

The localized functions retain exactly the available finite regularity.
Their derivative bounds are uniform in the half-integer localization
center, and retain the spatial decay of the original S norm.
-/

@[expose] public section
set_option autoImplicit false

open Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.SumintPar

/-- A weight multiplied by one smooth partition piece. -/
@[expose] noncomputable def localizedWeight {d : ℕ} (a : Fin d → ℤ)
    (F : Mom d → ℂ) (x : Mom d) : ℂ := localizationProfile a x • F x

/-- Finite regularity is preserved without strengthening the source assumptions. -/
theorem localizedWeight_contDiff {d N : ℕ} (a : Fin d → ℤ) {F : Mom d → ℂ}
    (hf : ContDiff ℝ N F) : ContDiff ℝ N (localizedWeight a F) :=
  ((localizationProfile_contDiff a).of_le (by simp)).smul hf

/-- The cutoff supplies compact support even when the original weight is not compactly supported. -/
theorem localizedWeight_hasCompactSupport {d : ℕ} (a : Fin d → ℤ) (F : Mom d → ℂ) :
    HasCompactSupport (localizedWeight a F) := by
  change HasCompactSupport (localizationProfile a • F)
  exact (localizationProfile_hasCompactSupport a).smul_right

/-- The explicit dimension/order constant in the localized Leibniz estimate. -/
@[expose] noncomputable def localizedDerivativeFactor (d n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
    ((2 : ℝ) ^ i * ApproxNT.thetaDerivConst d i) * (d : ℝ) ^ (n - i)

/-- This coefficient is nonnegative. -/
theorem localizedDerivativeFactor_nonneg (d n : ℕ) : 0 ≤ localizedDerivativeFactor d n := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
    (ApproxNT.thetaDerivConst_nonneg d i))) (by positivity)

/-- Every localized Fréchet derivative keeps the source spatial decay, with a uniform explicit factor. -/
theorem norm_iteratedFDeriv_localizedWeight_le {d N K n : ℕ} (hN : N ≠ 0) (hn : n ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (a : Fin d → ℤ) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ ≤
      localizedDerivativeFactor d n * (B / jbr x ^ K) := by
  have hf := contDiff_of_SNorm_le hN hF
  have hc : ContDiff ℝ N (localizationProfile a) := (localizationProfile_contDiff a).of_le (by simp)
  have ho : (n : ℕ∞ω) ≤ N := by exact_mod_cast hn
  have hp : 0 ≤ B / jbr x ^ K := div_nonneg hB (pow_nonneg (by linarith [one_le_jbr x]) _)
  apply (norm_iteratedFDeriv_smul_le hc hf x ho).trans
  calc
    _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
        ((2 : ℝ) ^ i * ApproxNT.thetaDerivConst d i) *
          ((d : ℝ) ^ (n - i) * (B / jbr x ^ K)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_localizationProfile_le a i x)
          (Nat.cast_nonneg _)
      · exact norm_iteratedFDeriv_le_of_SNorm_le hN ((Nat.sub_le n i).trans hn) hB hF x
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
          (ApproxNT.thetaDerivConst_nonneg d i))
    _ = _ := by
      unfold localizedDerivativeFactor
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end WaveTurbulence.SumintPar
