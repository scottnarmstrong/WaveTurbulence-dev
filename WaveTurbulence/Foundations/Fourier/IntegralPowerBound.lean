/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# A finite-measure power estimate for nonnegative integrals

This form of Hölder is convenient for integrating a time primitive along
one coordinate before taking its `Lᵖ` norm.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Hölder with the constant function, raised to the input exponent. -/
theorem lintegral_rpow_le_measure_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ} (hp : 1 < p) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ p ≤ μ Set.univ ^ (p - 1) * ∫⁻ x, f x ^ p ∂μ := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf
    (aemeasurable_const : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, mul_one] at h
  have hh := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hpq.pos.ne', ENNReal.rpow_one] at hh
  have he : (1 / Real.conjExponent p) * p = p - 1 := by
    have hi := hpq.inv_add_inv_eq_one
    field_simp at hi ⊢
    nlinarith
  rw [he] at hh
  simpa only [one_mul, mul_comm] using hh

end WaveTurbulence.Fourier
