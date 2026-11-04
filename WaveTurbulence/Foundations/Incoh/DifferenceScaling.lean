/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Scaling the zeroth and first frequency moments

TARGET (incohproof14)–(incohproof15): the time-difference scale
`lam = δ L^(2γ)` contributes `lam⁻¹`, or `lam⁻²` for separated layers.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Positive dilation in a scalar nonnegative integral. -/
theorem lintegral_comp_pos_mul {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ r : ℝ, f (lam * r)) = ENNReal.ofReal lam⁻¹ * ∫⁻ s : ℝ, f s := by
  have hmul : Measurable (fun r : ℝ => lam * r) := measurable_const.mul measurable_id
  rw [← lintegral_map hf hmul]
  have hm : Measure.map (fun r : ℝ => lam * r) volume = ENNReal.ofReal lam⁻¹ • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hlam)] using
      Measure.map_addHaar_smul (volume : Measure ℝ) hlam.ne'
  rw [hm, lintegral_smul_measure, smul_eq_mul]

/-- The extra factor of the time difference produces a second inverse dilation factor. -/
theorem lintegral_firstMoment_comp_pos_mul {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ r : ℝ, f (lam * r) * ENNReal.ofReal |r|) =
      (ENNReal.ofReal lam⁻¹) ^ 2 * ∫⁻ s : ℝ, f s * ENNReal.ofReal |s| := by
  have hg : Measurable (fun s : ℝ => f s * ENNReal.ofReal |s|) :=
    hf.mul (ENNReal.measurable_ofReal.comp continuous_abs.measurable)
  have heq (r : ℝ) : f (lam * r) * ENNReal.ofReal |r| =
      ENNReal.ofReal lam⁻¹ * (f (lam * r) * ENNReal.ofReal |lam * r|) := by
    have hr : |r| = lam⁻¹ * |lam * r| := by
      rw [abs_mul, abs_of_pos hlam, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
    rw [hr, ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le)]
    ac_rfl
  simp_rw [heq]
  have hmul : Measurable (fun r : ℝ => lam * r) := measurable_const.mul measurable_id
  have hg' : AEMeasurable (fun r : ℝ => f (lam * r) * ENNReal.ofReal |lam * r|) :=
    (hg.comp hmul).aemeasurable
  rw [lintegral_const_mul'' _ hg',
    lintegral_comp_pos_mul hlam hg, pow_two, mul_assoc]

end WaveTurbulence.Incoh
