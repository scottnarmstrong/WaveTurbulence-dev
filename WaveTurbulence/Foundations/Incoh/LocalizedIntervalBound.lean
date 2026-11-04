/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalizedInterval
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# A single cutoff-dependent first-variation bound

The same positive constant controls every localized interval, independent
of its endpoints and smoothing width.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Uniform mass and first variation for all literal localized interval approximations. -/
theorem exists_localizedInterval_firstVariation_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ ε a b : ℝ, 0 < ε → a ≤ b →
      (∫ x, ‖localizedInterval χ ε a b x‖) ≤ B ∧
      (∫ x, ‖deriv (localizedInterval χ ε a b) x‖) ≤ B := by
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  let B := 1 + (∫ x, ‖χ x‖) + (∫ x, ‖deriv χ x‖) + 2 * h.bound
  have h0 : 0 ≤ ∫ x, ‖χ x‖ := integral_nonneg (fun _ => norm_nonneg _)
  have h1 : 0 ≤ ∫ x, ‖deriv χ x‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hC := h.one_le_bound
  refine ⟨B, by dsimp only [B]; linarith, ?_⟩
  intro ε a b hε hab
  constructor
  · exact (integral_norm_localizedInterval_le hχ hcχ hε hab).trans (by dsimp only [B]; linarith)
  · exact (integral_norm_deriv_localizedInterval_le hχ hcχ h hε hab).trans (by dsimp only [B]; linarith)

/-- Restricting the scalar window mass to any box preserves the uniform bound. -/
theorem setLIntegral_norm_localizedInterval_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {ε a b B : ℝ}
    (hm : (∫ x, ‖localizedInterval χ ε a b x‖) ≤ B) (R : ℝ) :
    (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖localizedInterval χ ε a b x‖) ≤ ENNReal.ofReal B := by
  have hi : Integrable (localizedInterval χ ε a b) := (contDiff_localizedInterval hχ ε a b).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_localizedInterval hcχ ε a b)
  apply (lintegral_mono_set (subset_univ _)).trans
  rw [Measure.restrict_univ]
  simpa only [ofReal_norm] using
    ((ofReal_integral_norm_eq_lintegral_enorm hi).symm.le.trans (ENNReal.ofReal_le_ofReal hm))

/-- The same restriction principle holds for the scalar first variation. -/
theorem setLIntegral_norm_deriv_localizedInterval_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {ε a b B : ℝ}
    (hm : (∫ x, ‖deriv (localizedInterval χ ε a b) x‖) ≤ B) (R : ℝ) :
    (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖deriv (localizedInterval χ ε a b) x‖) ≤ ENNReal.ofReal B := by
  have hi : Integrable (deriv (localizedInterval χ ε a b)) := ((contDiff_localizedInterval hχ ε a b).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
    (hasCompactSupport_localizedInterval hcχ ε a b).deriv
  apply (lintegral_mono_set (subset_univ _)).trans
  rw [Measure.restrict_univ]
  simpa only [ofReal_norm] using
    ((ofReal_integral_norm_eq_lintegral_enorm hi).symm.le.trans (ENNReal.ofReal_le_ofReal hm))

end WaveTurbulence.Incoh
