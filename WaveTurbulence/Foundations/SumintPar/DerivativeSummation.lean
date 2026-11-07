/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.FiniteOverlap
public import WaveTurbulence.Foundations.SumintPar.SpatialTail
public import WaveTurbulence.Foundations.SumintPar.CellIntegralBounds
import Mathlib.Tactic

/-!
# Summing localized derivative L1 integrals over all centers

Finite overlap is used before integrating in momentum. The spatial tail
from the source S norm is therefore paid only once, rather than once for
each localization center.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- The pointwise sum of all localized derivatives has the original integrable spatial decay. -/
theorem tsum_enorm_localized_derivative_le {d N K n : ℕ} (hN : N ≠ 0) (hn : n ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (x : Mom d) :
    (∑' a : Fin d → ℤ, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ₑ) ≤
      ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) * inverseSpatialWeight K x) := by
  have hz (a : Fin d → ℤ) (hx : x ∉ localizationBox a) :
      iteratedFDeriv ℝ n (localizedWeight a F) x = 0 := by
    by_contra hne
    exact hx ((tsupport_localizedWeight_subset a F) ((support_iteratedFDeriv_subset n) hne))
  have hh := tsum_enorm_le_localization_overlap
    (fun a : Fin d → ℤ => iteratedFDeriv ℝ n (localizedWeight a F) x) x hz
    (fun a => norm_iteratedFDeriv_localizedWeight_le hN hn hB hF a x)
  apply hh.trans_eq
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ d)]
  congr 1
  unfold inverseSpatialWeight
  ring

/-- Tonelli and the integrable source tail sum the real derivative integrals over every localization center. -/
theorem tsum_localized_derivative_L1_le {d N K n : ℕ} (hN : N ≠ 0) (hn : n ≤ N) (hK : d < K)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (∫ x, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖)) ≤
      ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) * ∫ x : Mom d, inverseSpatialWeight K x) := by
  have hf := contDiff_of_SNorm_le hN hF
  have hi (a : Fin d → ℤ) := integrable_iteratedFDeriv_localizedWeight hn hf a
  have hm (a : Fin d → ℤ) : Measurable (fun x => ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ₑ) :=
    ((localizedWeight_contDiff a hf).continuous_iteratedFDeriv (by exact_mod_cast hn)).enorm.measurable
  have he (a : Fin d → ℤ) : ENNReal.ofReal (∫ x, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖) =
      ∫⁻ x, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ₑ :=
    ofReal_integral_norm_eq_lintegral_enorm (hi a)
  simp_rw [he]
  rw [← lintegral_tsum (fun a => (hm a).aemeasurable)]
  calc
    _ ≤ ∫⁻ x : Mom d, ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) *
        inverseSpatialWeight K x) := lintegral_mono (tsum_enorm_localized_derivative_le hN hn hB hF)
    _ = ENNReal.ofReal (∫ x : Mom d, ((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) *
        inverseSpatialWeight K x) := by
      apply (ofReal_integral_eq_lintegral_ofReal
        ((integrable_inverseSpatialWeight hK).const_mul _)
        (ae_of_all _ (fun x => mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
          (localizedDerivativeFactor_nonneg d n)) hB) (inverseSpatialWeight_nonneg K x)))).symm
    _ = _ := by rw [integral_const_mul]

end WaveTurbulence.SumintPar
