/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.RectanglePrimitive
public import WaveTurbulence.Foundations.Fourier.EndpointPowerBound
public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
public import WaveTurbulence.Foundations.Fourier.BoxFaceMarginals
import Mathlib.Tactic

/-!
# Power bounds for rectangular time primitives

Hölder on the fixed cutoff box controls the rectangle and each of its
boundary faces. The constants depend on the box width, not on input support.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Discarding an oriented interval inside the cutoff box. -/
theorem enorm_intervalIntegral_le_box {R : ℝ} (hR : 0 ≤ R) {t : ℝ}
    (ht : t ∈ Icc (-R) R) (f : ℝ → ℂ) :
    ‖∫ u in (0 : ℝ)..t, f u‖ₑ ≤ ∫⁻ u in Icc (-R) R, ‖f u‖ₑ := by
  apply (enorm_intervalIntegral_le f 0 t).trans
  exact lintegral_mono_set (uIoc_subset_uIcc.trans
    (uIcc_subset_Icc ⟨by linarith, hR⟩ ht))

/-- Rectangular primitive magnitude is bounded by the full amplitude box. -/
theorem enorm_rectanglePrimitive_le_box {R : ℝ} (hR : 0 ≤ R)
    (A : (Fin 2 → ℝ) → ℂ) (t : Fin 2 → ℝ)
    (ht : t ∈ Icc (fun _ => -R) (fun _ => R)) :
    ‖rectanglePrimitive A t‖ₑ ≤ boxIntegral 2 (fun v => ‖A v‖ₑ) R := by
  rw [rectanglePrimitive, boxIntegral_two]
  have ht0 : t 0 ∈ Icc (-R) R := ⟨ht.1 0, ht.2 0⟩
  have ht1 : t 1 ∈ Icc (-R) R := ⟨ht.1 1, ht.2 1⟩
  apply (enorm_intervalIntegral_le_box hR ht0 _).trans
  exact lintegral_mono fun u => enorm_intervalIntegral_le_box hR ht1 _

/-- The power of an amplitude box integral satisfies finite-measure Hölder. -/
theorem boxIntegral_two_rpow_le {p : ℝ} (hp : 1 < p)
    {f : (Fin 2 → ℝ) → ℝ≥0∞} (hf : Measurable f) (R : ℝ) :
    (boxIntegral 2 f R) ^ p ≤ (volume (Icc (-R) R) ^ 2) ^ (p - 1) *
      boxIntegral 2 (fun v => f v ^ p) R := by
  have he (g : (Fin 2 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
      boxIntegral 2 g R = ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), g t := by
    rw [lintegral_two_coordinates_box hg, boxIntegral_two]
  rw [he f hf, he _ (hf.pow_const p), ← volume_two_time_box R]
  have h := lintegral_rpow_le_measure_mul
    (volume.restrict (Icc (fun _ : Fin 2 => -R) (fun _ => R))) hp hf.aemeasurable.restrict
  simpa only [Measure.restrict_apply_univ] using h

/-- The base rectangle power integral over output time costs two box widths. -/
theorem lintegral_rectanglePrimitive_rpow_box_le {p R : ℝ} (hp : 1 < p) (hR : 0 ≤ R)
    {A : (Fin 2 → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R), ‖rectanglePrimitive A t‖ₑ ^ p) ≤
      ((volume (Icc (-R) R) ^ 2) * (volume (Icc (-R) R) ^ 2) ^ (p - 1)) *
        boxIntegral 2 (fun v => ‖A v‖ₑ ^ p) R := by
  calc
    _ ≤ ∫⁻ _t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
        (boxIntegral 2 (fun v => ‖A v‖ₑ) R) ^ p := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact ENNReal.rpow_le_rpow (enorm_rectanglePrimitive_le_box hR A t ht) (by linarith)
    _ = volume (Icc (-R) R) ^ 2 * (boxIntegral 2 (fun v => ‖A v‖ₑ) R) ^ p := by
      simp only [lintegral_const, Measure.restrict_apply_univ, volume_two_time_box, mul_comm]
    _ ≤ _ := (mul_le_mul_right (boxIntegral_two_rpow_le hp hA.enorm R) _).trans_eq (by ring)

/-- Integrating a row marginal over the output box costs the unused endpoint width. -/
theorem box_row_marginal {f : (Fin 2 → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      ∫⁻ v in Icc (-R) R, f ![t 0, v]) =
      volume (Icc (-R) R) * boxIntegral 2 f R := by
  have hm : Measurable (fun t : Fin 2 → ℝ => ∫⁻ v in Icc (-R) R, f ![t 0, v]) := by
    apply Measurable.lintegral_prod_right
    apply hf.comp
    apply Measurable.of_eval
    intro j
    fin_cases j
    · change Measurable (fun p : (Fin 2 → ℝ) × ℝ => p.1 0)
      fun_prop
    · change Measurable (fun p : (Fin 2 → ℝ) × ℝ => p.2)
      fun_prop
  rw [lintegral_two_coordinates_box hm, boxIntegral_two]
  simp only [Matrix.cons_val_zero, lintegral_const, Measure.restrict_apply_univ]
  rw [lintegral_mul_const' _ _ isCompact_Icc.measure_lt_top.ne, mul_comm]

/-- A row primitive has its power integral bounded by the input power integral. -/
theorem lintegral_rectangle_row_rpow_box_le {p R : ℝ} (hp : 1 < p) (hR : 0 ≤ R)
    {A : (Fin 2 → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      ‖∫ v in (0 : ℝ)..t 1, A ![t 0, v]‖ₑ ^ p) ≤
      (volume (Icc (-R) R) ^ (p - 1) * volume (Icc (-R) R)) *
        boxIntegral 2 (fun v => ‖A v‖ₑ ^ p) R := by
  have hs (u : ℝ) : Measurable (fun v : ℝ => ‖A ![u, v]‖ₑ) := by
    apply hA.enorm.comp
    apply Measurable.of_eval
    intro j
    fin_cases j
    · change Measurable (fun _ : ℝ => u)
      fun_prop
    · change Measurable (fun v : ℝ => v)
      fun_prop
  calc
    _ ≤ ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      volume (Icc (-R) R) ^ (p - 1) * ∫⁻ v in Icc (-R) R, ‖A ![t 0, v]‖ₑ ^ p := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply (ENNReal.rpow_le_rpow
        (enorm_intervalIntegral_le_box hR ⟨ht.1 1, ht.2 1⟩ _) (by linarith)).trans
      have hh := lintegral_rpow_le_measure_mul (volume.restrict (Icc (-R) R)) hp
        (hs (t 0)).aemeasurable.restrict
      simpa only [Measure.restrict_apply_univ] using hh
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        isCompact_Icc.measure_lt_top.ne), box_row_marginal (hA.enorm.pow_const p)]
      ring

/-- Integrating a column marginal costs the other unused endpoint width. -/
theorem box_column_marginal {f : (Fin 2 → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (R : ℝ) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      ∫⁻ u in Icc (-R) R, f ![u, t 1]) =
      volume (Icc (-R) R) * boxIntegral 2 f R := by
  have hm : Measurable (fun t : Fin 2 → ℝ => ∫⁻ u in Icc (-R) R, f ![u, t 1]) := by
    apply Measurable.lintegral_prod_right
    apply hf.comp
    apply Measurable.of_eval
    intro j
    fin_cases j
    · change Measurable (fun p : (Fin 2 → ℝ) × ℝ => p.2)
      fun_prop
    · change Measurable (fun p : (Fin 2 → ℝ) × ℝ => p.1 1)
      fun_prop
  rw [lintegral_two_coordinates_box hm, boxIntegral_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, lintegral_const, Measure.restrict_apply_univ]
  rw [mul_comm]
  congr 1
  exact lintegral_lintegral_swap (μ := volume.restrict (Icc (-R) R))
    (ν := volume.restrict (Icc (-R) R)) (f := fun s u : ℝ => f ![u, s])
    (hf.comp (by fun_prop)).aemeasurable

/-- A column primitive has its power integral bounded by the input power integral. -/
theorem lintegral_rectangle_column_rpow_box_le {p R : ℝ} (hp : 1 < p) (hR : 0 ≤ R)
    {A : (Fin 2 → ℝ) → ℂ} (hA : Measurable A) :
    (∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      ‖∫ v in (0 : ℝ)..t 0, A ![v, t 1]‖ₑ ^ p) ≤
      (volume (Icc (-R) R) ^ (p - 1) * volume (Icc (-R) R)) *
        boxIntegral 2 (fun v => ‖A v‖ₑ ^ p) R := by
  have hs (u : ℝ) : Measurable (fun v : ℝ => ‖A ![v, u]‖ₑ) := by
    apply hA.enorm.comp
    apply Measurable.of_eval
    intro j
    fin_cases j
    · change Measurable (fun v : ℝ => v)
      fun_prop
    · change Measurable (fun _ : ℝ => u)
      fun_prop
  calc
    _ ≤ ∫⁻ t in Icc (fun _ : Fin 2 => -R) (fun _ => R),
      volume (Icc (-R) R) ^ (p - 1) * ∫⁻ v in Icc (-R) R, ‖A ![v, t 1]‖ₑ ^ p := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      apply (ENNReal.rpow_le_rpow
        (enorm_intervalIntegral_le_box hR ⟨ht.1 0, ht.2 0⟩ _) (by linarith)).trans
      have hh := lintegral_rpow_le_measure_mul (volume.restrict (Icc (-R) R)) hp
        (hs (t 1)).aemeasurable.restrict
      simpa only [Measure.restrict_apply_univ] using hh
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        isCompact_Icc.measure_lt_top.ne), box_column_marginal (hA.enorm.pow_const p)]
      ring

end WaveTurbulence.Fourier
