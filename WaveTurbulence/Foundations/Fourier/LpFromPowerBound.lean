/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# Converting power integrals into Lp operator estimates

The extended-valued form also covers inputs whose norm is infinite.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- A power integral bound yields an extended `Lᵖ` bound after taking roots. -/
theorem eLpNorm_le_of_power_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ} (hp : 0 < p) {f g : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {K : ℝ≥0∞} (h : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ K * ∫⁻ x, ‖g x‖ₑ ^ p ∂μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ K ^ (1 / p) * eLpNorm g (ENNReal.ofReal p) μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top hg, ENNReal.toReal_ofReal hp.le]
  exact (ENNReal.rpow_le_rpow h (by positivity)).trans_eq
    (ENNReal.mul_rpow_of_nonneg _ _ (by positivity))

end WaveTurbulence.Fourier
