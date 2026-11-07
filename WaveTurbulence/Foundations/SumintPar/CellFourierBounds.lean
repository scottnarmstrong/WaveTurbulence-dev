/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CellIntegralBounds
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev
import Mathlib.Tactic

/-!
# Fourier-L1 expansion bounds for a localized sumint weight

Only `d+1` of the `30d` available derivatives are used. The coefficient
is explicit, finite, and independent of the localization center. This
is the uniform local estimate required for the ℒ factors in Step 1.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped FourierTransform ENNReal

namespace WaveTurbulence.SumintPar

/-- A dimension-only Fourier-L1 coefficient for one localized weight. -/
@[expose] noncomputable def cellFourierFactor (d : ℕ) : ℝ :=
  Fourier.fourierL1Constant (Mom d) (d + 1) *
    ∑ j ∈ range (d + 2), localizedDerivativeFactor d j

/-- Nonnegativity of the local Fourier coefficient. -/
theorem cellFourierFactor_nonneg (d : ℕ) : 0 ≤ cellFourierFactor d :=
  mul_nonneg (Fourier.fourierL1Constant_nonneg _) (Finset.sum_nonneg fun j _ =>
    localizedDerivativeFactor_nonneg d j)

/-- The Fourier transform of each finite-regularity localized source weight is integrable, with a uniform bound. -/
theorem localizedWeight_fourier_integrable_and_bound {d N K : ℕ} (hN : N ≠ 0)
    (hdN : d + 1 ≤ N) {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) (a : Fin d → ℤ) :
    Integrable (𝓕 (localizedWeight a F)) ∧
      (∫ ξ, ‖𝓕 (localizedWeight a F) ξ‖) ≤ cellFourierFactor d * B := by
  have hf := contDiff_of_SNorm_le hN hF
  have hc : ContDiff ℝ (d + 1) (localizedWeight a F) :=
    (localizedWeight_contDiff a hf).of_le (by exact_mod_cast hdN)
  have hi (j : ℕ) (hj : j ≤ d + 1) : Integrable (iteratedFDeriv ℝ j (localizedWeight a F)) :=
    integrable_iteratedFDeriv_localizedWeight (hj.trans hdN) hf a
  have hdim : Module.finrank ℝ (Mom d) < d + 1 := by simp [Mom]
  obtain ⟨hfi, hbound⟩ := Fourier.fourier_integrable_and_integral_norm_le hdim hc hi
  refine ⟨hfi, hbound.trans ?_⟩
  have hs : Fourier.derivativeL1Sum (d + 1) (localizedWeight a F) ≤
      (∑ j ∈ range (d + 2), localizedDerivativeFactor d j) * B := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ N := by
      have hh := Finset.mem_range.mp hj
      omega
    exact integral_norm_iteratedFDeriv_localizedWeight_le hN hj' hB hF a
  exact (mul_le_mul_of_nonneg_left hs (Fourier.fourierL1Constant_nonneg _)).trans_eq (by
    unfold cellFourierFactor
    ring)

/-- Pointwise Fourier inversion gives the actual modulation expansion of each localized source weight. -/
theorem localizedWeight_fourier_expansion {d N K : ℕ} (hN : N ≠ 0)
    (hdN : d + 1 ≤ N) {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) (a : Fin d → ℤ) (x : Mom d) :
    (∫ ξ : Mom d, (Real.fourierChar (inner ℝ ξ x) : ℂ) * 𝓕 (localizedWeight a F) ξ) =
      localizedWeight a F x := by
  have hf := localizedWeight_contDiff a (contDiff_of_SNorm_le hN hF)
  have hi : Integrable (localizedWeight a F) :=
    hf.continuous.integrable_of_hasCompactSupport (localizedWeight_hasCompactSupport a F)
  have hfi := (localizedWeight_fourier_integrable_and_bound hN hdN hB hF a).1
  have h := congrFun (hf.continuous.fourierInv_fourier_eq hi hfi) x
  simpa only [Real.fourierInv_eq, real_inner_comm, Circle.smul_def, smul_eq_mul] using h

end WaveTurbulence.SumintPar
