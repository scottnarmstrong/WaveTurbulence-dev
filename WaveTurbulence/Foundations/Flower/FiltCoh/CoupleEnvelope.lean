/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleScalar

/-! # FILT-COH: envelope of the whole physical scalar at an arbitrary time weight

The bound-only counterpart of main's `RA1Leafwise.physical_error_scalar_envelope`: there is no `L` gain (the sum
is not compared with its principal value) and the weight `θ` may be any value in `[0, 1 - η/8]`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- The NT normalizer mass is at most the Wick-type mass (with `4A` and the factor `4^n`). -/
theorem sum_mass_le_wick_mass (n : ℕ) {N A : ℝ} (_hN : 0 ≤ N) (hA : 0 ≤ A) (G : ℝ≥0∞) :
    ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) + G ≤
      (4:ℝ≥0∞)^n*((ENNReal.ofReal N*∑' k : ℕ,
        ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) + G) := by
  have ht : (∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) ≤
      ∑' k : ℕ, ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial) := by
    refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
    have hp : A^k ≤ (4*A)^k := pow_le_pow_left₀ hA (by linarith) k
    have hf : (0:ℝ) ≤ ((2*k).factorial:ℝ)/(4*k).factorial := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hp hf
  have h1 : (1:ℝ≥0∞) ≤ (4:ℝ≥0∞)^n := one_le_pow₀ (by norm_num)
  calc _ ≤ ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) + G :=
        by gcongr
    _ = 1*((ENNReal.ofReal N*∑' k : ℕ,
        ENNReal.ofReal ((4*A)^k*((2*k).factorial:ℝ)/(4*k).factorial)) + G) := by rw [one_mul]
    _ ≤ _ := by gcongr

end WaveTurbulence.Flower.FiltCoh
