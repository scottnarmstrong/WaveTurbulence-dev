/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CellFourierBounds
public import WaveTurbulence.Foundations.Sumint.DerivativeSummation
import Mathlib.Tactic

/-!
# Summed Fourier-L1 bounds for the decaying sumint weights

The original spatial decay is integrated once after the finite-overlap
bound. Consequently the sum over all localization centers has a
constant depending only on dimension and the spatial weight order.
-/

public section

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.Sumint

/-- Extended nonnegative sums commute with finite sums without a summability premise. -/
theorem tsum_finsetSum_ennreal {α ι : Type*} (s : Finset ι) (f : α → ι → ℝ≥0∞) :
    (∑' a, ∑ j ∈ s, f a j) = ∑ j ∈ s, ∑' a, f a j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp only [Finset.sum_insert hj, ENNReal.tsum_add, ih]

/-- The dimension/weight-order constant for all localized Fourier masses together. -/
@[expose] noncomputable def summedCellFourierFactor (d K : ℕ) : ℝ :=
  Fourier.fourierL1Constant (Mom d) (d + 1) *
    ∑ j ∈ range (d + 2), ((4 : ℝ) ^ d * localizedDerivativeFactor d j *
      ∫ x : Mom d, inverseSpatialWeight K x)

/-- Nonnegativity of every real coefficient in the summed bound. -/
theorem summedCellFourierFactor_nonneg (d K : ℕ) : 0 ≤ summedCellFourierFactor d K := by
  apply mul_nonneg (Fourier.fourierL1Constant_nonneg _)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (by positivity) (localizedDerivativeFactor_nonneg d j))
    (integral_nonneg (inverseSpatialWeight_nonneg K))

/-- Retain the actual derivative L1 integrals in the single-cell Sobolev bound. -/
theorem cell_fourier_mass_le_derivatives {d N K : ℕ} (hN : N ≠ 0) (hdN : d + 1 ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hF : SNorm N K F ≤ ENNReal.ofReal B) (a : Fin d → ℤ) :
    ENNReal.ofReal (∫ ξ, ‖𝓕 (localizedWeight a F) ξ‖) ≤
      ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ENNReal.ofReal (∫ x, ‖iteratedFDeriv ℝ j (localizedWeight a F) x‖) := by
  have hf := contDiff_of_SNorm_le hN hF
  have hc : ContDiff ℝ (d + 1) (localizedWeight a F) :=
    (localizedWeight_contDiff a hf).of_le (by exact_mod_cast hdN)
  have hi (j : ℕ) (hj : j ≤ d + 1) := integrable_iteratedFDeriv_localizedWeight (hj.trans hdN) hf a
  have hdim : Module.finrank ℝ (Mom d) < d + 1 := by simp [Mom]
  have hb := (Fourier.fourier_integrable_and_integral_norm_le hdim hc hi).2
  apply (ENNReal.ofReal_le_ofReal hb).trans_eq
  rw [ENNReal.ofReal_mul (Fourier.fourierL1Constant_nonneg _)]
  congr 1
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

/-- The total mass of all Fourier coefficients of localized decaying weights is controlled uniformly. -/
theorem tsum_localizedWeight_fourier_mass_le {d N K : ℕ} (hN : N ≠ 0) (hdN : d + 1 ≤ N)
    (hK : d < K) {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hF : SNorm N K F ≤ ENNReal.ofReal B) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (∫ ξ, ‖𝓕 (localizedWeight a F) ξ‖)) ≤
      ENNReal.ofReal (summedCellFourierFactor d K * B) := by
  have ht : 0 ≤ ∫ x : Mom d, inverseSpatialWeight K x :=
    integral_nonneg (inverseSpatialWeight_nonneg K)
  calc
    _ ≤ ∑' a : Fin d → ℤ, ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ENNReal.ofReal (∫ x, ‖iteratedFDeriv ℝ j (localizedWeight a F) x‖) :=
      ENNReal.tsum_le_tsum (fun a => cell_fourier_mass_le_derivatives hN hdN hF a)
    _ = ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ∑' a : Fin d → ℤ,
          ENNReal.ofReal (∫ x, ‖iteratedFDeriv ℝ j (localizedWeight a F) x‖) := by
      rw [ENNReal.tsum_mul_left, tsum_finsetSum_ennreal]
    _ ≤ ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d j * B) *
          ∫ x : Mom d, inverseSpatialWeight K x) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j hj
      apply tsum_localized_derivative_L1_le hN _ hK hB hF
      have hh := Finset.mem_range.mp hj
      omega
    _ = _ := by
      unfold summedCellFourierFactor
      rw [mul_assoc (Fourier.fourierL1Constant (Mom d) (d + 1))]
      rw [ENNReal.ofReal_mul (Fourier.fourierL1Constant_nonneg _)]
      congr 1
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      · intro j _
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
          (localizedDerivativeFactor_nonneg d j)) ht) hB

end WaveTurbulence.Sumint
