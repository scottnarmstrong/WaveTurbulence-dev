/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeOperatorRegularity
public import WaveTurbulence.Foundations.Fourier.EndpointL1Bound
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Input cutoff localization from Lp to L1

Only a fixed box determined by the cutoff enters the Hölder constant.
This estimate applies to arbitrary measurable representatives and supplies
the finite-norm approximation step in TARGET A.2.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The local Hölder factor after the two input cutoffs. -/
@[expose] noncomputable def localTimeL1Factor (p R C : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C ^ 2) * (volume (Icc (-R) R) ^ 2) ^ (1 - 1 / p)

/-- Finiteness holds for every `p ≥ 1`. -/
theorem localTimeL1Factor_ne_top {p : ℝ} (hp : 1 ≤ p) (R C : ℝ) :
    localTimeL1Factor p R C ≠ ⊤ := by
  have he : 0 ≤ 1 - 1 / p := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
    norm_num at this
    simpa only [one_div] using sub_nonneg.mpr this
  have hw : volume (Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  unfold localTimeL1Factor
  finiteness

/-- Arbitrary measurable amplitudes become `L¹` after localization, with a local Hölder bound. -/
theorem eLpNorm_triangleAmplitude_one_le {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {F : (Fin 2 → ℝ) → ℂ} (hF : AEStronglyMeasurable F volume) :
    eLpNorm (triangleAmplitude χ F) 1 ≤
      localTimeL1Factor p h.radius h.bound * eLpNorm F (ENNReal.ofReal p) := by
  have hC : 0 ≤ h.bound := le_trans (by norm_num) h.one_le_bound
  have hAmp : AEStronglyMeasurable (triangleAmplitude χ F) volume :=
    (coordinateCutoff_contDiff hχ).continuous.aestronglyMeasurable.mul hF
  have he : triangleAmplitude χ F = fun t : Fin 2 → ℝ =>
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * F t := by
    funext t
    simp [triangleAmplitude, coordinateCutoff, Fin.prod_univ_two, mul_assoc]
  let S := Icc (fun _ : Fin 2 => -h.radius) (fun _ => h.radius)
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hl := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict S) hp1 hF.restrict
  simp only [Measure.restrict_apply_univ, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ p), div_one] at hl
  rw [eLpNorm_one_eq_lintegral_enorm hAmp, he]
  apply (lintegral_enorm_endpoint_product_le hC h.endpointBounds h.endpointBounds F).trans
  have ht : (∫⁻ t in S, ‖F t‖ₑ) = eLpNorm F 1 (volume.restrict S) :=
    (eLpNorm_one_eq_lintegral_enorm hF.restrict).symm
  change ENNReal.ofReal (h.bound ^ 2) * (∫⁻ t in S, ‖F t‖ₑ) ≤ _
  rw [ht]
  apply (mul_le_mul_right hl _).trans
  have hrest := eLpNorm_restrict_le F (ENNReal.ofReal p) volume S
  apply (mul_le_mul_right (mul_le_mul_left hrest _) _).trans_eq
  dsimp [localTimeL1Factor, S]
  rw [volume_two_time_box]
  ring

/-- Finite input `Lᵖ` norm implies integrability of the localized amplitude. -/
theorem triangleAmplitude_integrable_of_memLp {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {F : (Fin 2 → ℝ) → ℂ} (hF : MemLp F (ENNReal.ofReal p)) :
    Integrable (triangleAmplitude χ F) := by
  apply memLp_one_iff_integrable.mp
  apply (eLpNorm_triangleAmplitude_one_le hp hχ h hF.aestronglyMeasurable).trans_lt
  exact ENNReal.mul_lt_top (localTimeL1Factor_ne_top hp _ _).lt_top hF.eLpNorm_lt_top

end WaveTurbulence.Fourier
