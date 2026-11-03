/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueBounds

/-!
# The integrable remainder in a principal-value Fourier integral

Subtracting the value at zero on the unit interval leaves an absolutely
integrable quotient. Its bound depends on the test function's Lipschitz
constant and `L¹` norm, without differentiating a Fourier phase.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace WaveTurbulence.Resonant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The remainder after subtracting the value at zero on the symmetric unit interval. -/
@[expose] noncomputable def pvRemainder (f : ℝ → E) (u : ℝ) : E :=
  u⁻¹ • (f u - (Icc (-1 : ℝ) 1).indicator (fun _ => f 0) u)

/-- Pointwise cancellation bound for the remainder. -/
theorem norm_pvRemainder_le {f : ℝ → E} {K : ℝ≥0} (hL : LipschitzWith K f) (u : ℝ) :
    ‖pvRemainder f u‖ ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (K : ℝ)) u + ‖f u‖ := by
  unfold pvRemainder
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hu, indicator_of_mem hu, norm_smul, Real.norm_eq_abs, abs_inv]
    have hh : ‖f u - f 0‖ ≤ (K : ℝ) * |u| := by
      simpa only [dist_eq_norm, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hL.dist_le_mul u 0
    calc |u|⁻¹ * ‖f u - f 0‖ ≤ |u|⁻¹ * ((K : ℝ) * |u|) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ K := by
        by_cases hz : u = 0
        · simp [hz]
        · rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr hz), mul_one]
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, sub_zero, zero_add,
      norm_smul, Real.norm_eq_abs, abs_inv]
    have hh : 1 ≤ |u| := by
      by_contra hn
      exact hu (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hh)

/-- Integrability follows from cancellation near zero and `L¹` decay at infinity. -/
theorem integrable_pvRemainder {f : ℝ → E} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) : Integrable (pvRemainder f) := by
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ => (K : ℝ))) :=
    (integrableOn_const (C := (K : ℝ)) (s := Icc (-1 : ℝ) 1)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hm : AEStronglyMeasurable (pvRemainder f) := by
    unfold pvRemainder
    exact measurable_id.inv.aestronglyMeasurable.smul
      (hf.aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator measurableSet_Icc))
  exact (hi.add hf.norm).mono' hm (Filter.Eventually.of_forall (norm_pvRemainder_le hL))

/-- Explicit absolute integral bound used before restoring the Fourier phase. -/
theorem integral_norm_pvRemainder_le {f : ℝ → E} {K : ℝ≥0}
    (hf : Integrable f) (hL : LipschitzWith K f) :
    (∫ u : ℝ, ‖pvRemainder f u‖) ≤ 2 * K + ∫ u : ℝ, ‖f u‖ := by
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ => (K : ℝ))) :=
    (integrableOn_const (C := (K : ℝ)) (s := Icc (-1 : ℝ) 1)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  refine (integral_mono (integrable_pvRemainder hf hL).norm (hi.add hf.norm)
    (norm_pvRemainder_le hL)).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add hi hf.norm, integral_indicator measurableSet_Icc]
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc]
  norm_num

end WaveTurbulence.Resonant
