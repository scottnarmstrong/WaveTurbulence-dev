/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PositiveFrequencyEnvelope
public import WaveTurbulence.Foundations.Fourier.HausdorffYoung
import Mathlib.Tactic

/-!
# Hölder and Hausdorff–Young for the positive-frequency multiplier

This estimate is applied separately to the actual endpoint derivatives
of the cutoff rectangle.
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Fourier

/-- One weighted Fourier integral is controlled by the input `Lᵖ` norm. -/
theorem lintegral_positiveEnvelope_fourier_le {η p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p ≤ 2)
    {f : (Fin 2 → ℝ) → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p)) :
    (∫⁻ ξ, ENNReal.ofReal (positiveFrequencyEnvelope η ξ) * ‖timeFourier f ξ‖ₑ) ≤
      positiveFrequencyFactor η p * eLpNorm f (ENNReal.ofReal p) := by
  have hw : Measurable (fun ξ : Fin 2 → ℝ => ENNReal.ofReal (positiveFrequencyEnvelope η ξ)) := by
    unfold positiveFrequencyEnvelope inverseBracketPower
    fun_prop
  have hfour : AEStronglyMeasurable (timeFourier f) volume := (timeFourier_continuous hf).aestronglyMeasurable
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hw.aemeasurable hfour.enorm
  change (∫⁻ ξ, ENNReal.ofReal (positiveFrequencyEnvelope η ξ) * ‖timeFourier f ξ‖ₑ) ≤ _ at hh
  have he : (∫⁻ ξ, ‖timeFourier f ξ‖ₑ ^ q) ^ (1 / q) =
      eLpNorm (timeFourier f) (ENNReal.ofReal q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top hfour, ENNReal.toReal_ofReal hpq.symm.nonneg]
  rw [he] at hh
  have hhy := timeFourier_hausdorffYoung hpq.lt.le hp2 hf hfp
  let : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := hpq.ennrealOfReal
  rw [ENNReal.HolderConjugate.conjExponent_eq (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal q)] at hhy
  exact hh.trans (mul_le_mul_right hhy _)

end WaveTurbulence.Fourier
