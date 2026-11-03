/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TwoTimeKernels
public import WaveTurbulence.Foundations.Fourier.EndpointL1Bound
public import WaveTurbulence.Foundations.Fourier.CutoffControl
public import WaveTurbulence.Foundations.Fourier.OrderedFaceRegularity
import Mathlib.Tactic

/-!
# L1 continuity of bounded time kernels with output cutoffs

All statements here apply to integrable amplitudes, with no continuity
assumption. They supply the continuity step for smooth approximation in A.2.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- A bounded time kernel followed by the two output cutoffs. -/
@[expose] noncomputable def cutoffKernelIntegral (χ : ℝ → ℝ)
    (K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ) (A : (Fin 2 → ℝ) → ℂ)
    (t : Fin 2 → ℝ) : ℂ :=
  (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * ∫ v, K t v * A v

/-- Joint measurability of the kernel suffices for the output integral. -/
theorem cutoffKernelIntegral_aestronglyMeasurable {χ : ℝ → ℝ} (hχ : Continuous χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K p.1 p.2))
    {A : (Fin 2 → ℝ) → ℂ} (hA : AEStronglyMeasurable A volume) :
    AEStronglyMeasurable (cutoffKernelIntegral χ K A) volume := by
  have hm : AEStronglyMeasurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      K p.1 p.2 * A p.2) (volume.prod volume) :=
    hK.aestronglyMeasurable.mul hA.comp_snd
  have hi := hm.integral_prod_right'
  have hc : Continuous (fun t : Fin 2 → ℝ => (χ (t 0) : ℂ) * (χ (t 1) : ℂ)) := by fun_prop
  exact hc.aestronglyMeasurable.mul hi

/-- The common `L¹` continuity factor of the output cutoff. -/
@[expose] noncomputable def cutoffKernelL1Factor (R C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R) ^ 2

/-- The continuity factor is finite for every real radius and bound. -/
theorem cutoffKernelL1Factor_ne_top (R C : ℝ) : cutoffKernelL1Factor R C ≠ ⊤ := by
  have hw : volume (Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  unfold cutoffKernelL1Factor
  finiteness

/-- A unit-bounded kernel has a uniform cutoff-output `L¹` estimate. -/
theorem lintegral_enorm_cutoffKernelIntegral_le {χ : ℝ → ℝ} (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ} (hKn : ∀ t v, ‖K t v‖ ≤ 1)
    (A : (Fin 2 → ℝ) → ℂ) :
    (∫⁻ t, ‖cutoffKernelIntegral χ K A t‖ₑ) ≤
      cutoffKernelL1Factor h.radius h.bound * ∫⁻ v, ‖A v‖ₑ := by
  have hC : 0 ≤ h.bound := le_trans (by norm_num) h.one_le_bound
  apply (lintegral_enorm_endpoint_product_le hC h.endpointBounds h.endpointBounds _).trans
  have hb (t : Fin 2 → ℝ) : ‖∫ v, K t v * A v‖ₑ ≤ ∫⁻ v, ‖A v‖ₑ := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono
    intro v
    change ‖K t v * A v‖ₑ ≤ ‖A v‖ₑ
    rw [enorm_mul]
    have hh : ‖K t v‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      simpa using ENNReal.ofReal_le_ofReal (hKn t v)
    exact (mul_le_mul' hh le_rfl).trans_eq (one_mul _)
  calc
    _ ≤ ENNReal.ofReal (h.bound ^ 2) *
      ∫⁻ _t in Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius), ∫⁻ v, ‖A v‖ₑ := by
      apply mul_le_mul_right
      exact lintegral_mono hb
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, volume_two_time_box]
      unfold cutoffKernelL1Factor
      ring

/-- Integrable amplitudes produce integrable cutoff outputs. -/
theorem cutoffKernelIntegral_integrable {χ : ℝ → ℝ} (hχ : Continuous χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K p.1 p.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {A : (Fin 2 → ℝ) → ℂ} (hA : Integrable A) :
    Integrable (cutoffKernelIntegral χ K A) := by
  refine ⟨cutoffKernelIntegral_aestronglyMeasurable hχ hK hA.aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  apply (lintegral_enorm_cutoffKernelIntegral_le h hKn A).trans_lt
  exact ENNReal.mul_lt_top (cutoffKernelL1Factor_ne_top _ _).lt_top
    (hasFiniteIntegral_iff_enorm.mp hA.hasFiniteIntegral)

/-- The kernel transform commutes with subtraction on integrable amplitudes. -/
theorem cutoffKernelIntegral_sub {χ : ℝ → ℝ}
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K p.1 p.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {A B : (Fin 2 → ℝ) → ℂ}
    (hA : Integrable A) (hB : Integrable B) :
    cutoffKernelIntegral χ K (fun v => A v - B v) =
      fun t => cutoffKernelIntegral χ K A t - cutoffKernelIntegral χ K B t := by
  funext t
  simp only [cutoffKernelIntegral, mul_sub, integral_sub
    (integrable_timeKernel_mul hK hKn hA t) (integrable_timeKernel_mul hK hKn hB t)]

end WaveTurbulence.Fourier
