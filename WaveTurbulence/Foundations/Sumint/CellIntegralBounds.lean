/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizationBox
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# L1 bounds of localized weight derivatives

The unit-volume support cube converts the already proved pointwise
finite-order bounds into integrable derivative bounds, uniformly in the
localization center.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Uniform pointwise derivative bounds after dropping spatial decay. -/
theorem norm_iteratedFDeriv_localizedWeight_le_const {d N K n : ℕ}
    (hN : N ≠ 0) (hn : n ≤ N) {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) (a : Fin d → ℤ) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ ≤ localizedDerivativeFactor d n * B := by
  apply (norm_iteratedFDeriv_localizedWeight_le hN hn hB hF a x).trans
  apply mul_le_mul_of_nonneg_left _ (localizedDerivativeFactor_nonneg d n)
  exact div_le_self hB (one_le_pow₀ (one_le_jbr x))

/-- The actual derivatives are integrable at every available order. -/
theorem integrable_iteratedFDeriv_localizedWeight {d N n : ℕ} (hn : n ≤ N)
    {F : Mom d → ℂ} (hf : ContDiff ℝ N F) (a : Fin d → ℤ) :
    Integrable (iteratedFDeriv ℝ n (localizedWeight a F)) := by
  have hc := localizedWeight_contDiff a hf
  have hcont : Continuous (iteratedFDeriv ℝ n (localizedWeight a F)) :=
    hc.continuous_iteratedFDeriv (by exact_mod_cast hn)
  exact hcont.integrable_of_hasCompactSupport ((localizedWeight_hasCompactSupport a F).iteratedFDeriv n)

/-- Its derivative L1 integrals have the same explicit dimension/order bound. -/
theorem integral_norm_iteratedFDeriv_localizedWeight_le {d N K n : ℕ}
    (hN : N ≠ 0) (hn : n ≤ N) {F : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B) (a : Fin d → ℤ) :
    (∫ x, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖) ≤ localizedDerivativeFactor d n * B := by
  have hz (x : Mom d) (hx : x ∉ localizationBox a) :
      ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ = 0 := by
    have hd : iteratedFDeriv ℝ n (localizedWeight a F) x = 0 := by
      by_contra hne
      exact hx ((tsupport_localizedWeight_subset a F) ((support_iteratedFDeriv_subset n) hne))
    rw [hd, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ‖∫ x in localizationBox a, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self
        (∫ x in localizationBox a, ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖)
    _ ≤ (localizedDerivativeFactor d n * B) * volume.real (localizationBox a) := by
      apply norm_setIntegral_le_of_norm_le_const (by rw [volume_localizationBox]; norm_num)
      intro x _
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_iteratedFDeriv_localizedWeight_le_const hN hn hB hF a x
    _ = _ := by simp only [Measure.real, volume_localizationBox, ENNReal.toReal_one, mul_one]

end WaveTurbulence.Sumint
