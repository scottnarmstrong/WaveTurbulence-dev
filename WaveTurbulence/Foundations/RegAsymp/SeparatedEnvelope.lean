/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.MCSRep
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Weighted masses of separated source-frequency envelopes -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped ENNReal

/-- An exceptional set in the source frequency is harmless even when the
pointwise estimate holds simultaneously for every spatial sample. -/
theorem weighted_lintegral_le_separated {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (η : ℝ)
    (v : (ℝ × ℝ) × U → ℝ) (hv : Measurable v)
    (E : U → ℝ≥0∞) (hE : Measurable E) (B : (ℝ × ℝ) → ℝ) (hB : Measurable B) {C : ℝ≥0∞}
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ u, ENNReal.ofReal (v (lam,u)) ≤ C * ENNReal.ofReal (B lam) * E u) :
    (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) ≤
      C * (∫⁻ lam, wL η lam * ENNReal.ofReal (B lam)) * (∫⁻ u, E u ∂μ) := by
  have heq : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) =
      ∫⁻ lam, ∫⁻ u, wL η lam * ENNReal.ofReal (v (lam,u)) ∂μ :=
    lintegral_prod _ (((measurable_wL η).comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp hv)).aemeasurable
  rw [heq]
  calc
    _ ≤ ∫⁻ lam, ∫⁻ u, wL η lam * (C * ENNReal.ofReal (B lam) * E u) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hb] with lam hlam
      exact lintegral_mono (fun u => mul_le_mul' le_rfl (hlam u))
    _ = ∫⁻ lam, C * (wL η lam * ENNReal.ofReal (B lam)) * (∫⁻ u, E u ∂μ) := by
      apply lintegral_congr
      intro lam
      simp_rw [← mul_assoc]
      rw [lintegral_const_mul _ hE]
      ac_rfl
    _ = _ := by
      have hm := (measurable_wL η).mul (ENNReal.measurable_ofReal.comp hB)
      have hmul : (∫⁻ lam, C * (wL η lam * ENNReal.ofReal (B lam)) * (∫⁻ u, E u ∂μ)) =
          (∫⁻ lam, C * (wL η lam * ENNReal.ofReal (B lam))) * (∫⁻ u, E u ∂μ) :=
        lintegral_mul_const'' _ (measurable_const.mul hm).aemeasurable
      rw [hmul]
      congr 1
      exact lintegral_const_mul C hm

/-- A finite source-weighted envelope mass gives the physical sample L1
hypothesis required for differentiating the actual spectral mixture. -/
theorem integrable_of_weighted_lintegral_lt_top {U : Type*} [MeasurableSpace U]
    (μ : Measure U) {η : ℝ} (hη : 0 ≤ η)
    (v : (ℝ × ℝ) × U → ℝ) (hv : Measurable v) (hvn : ∀ q, 0 ≤ v q)
    (hfin : (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) < ⊤) :
    Integrable v (volume.prod μ) := by
  apply (lintegral_ofReal_ne_top_iff_integrable hv.aestronglyMeasurable
    (ae_of_all _ hvn)).mp
  apply ne_of_lt
  have hmass : (∫⁻ q, ENNReal.ofReal (v q) ∂volume.prod μ) ≤
      ∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ :=
    lintegral_mono (fun q => le_mul_of_one_le_left bot_le (one_le_wL hη q.1))
  exact hmass.trans_lt hfin

end WaveTurbulence.RegAsymp
