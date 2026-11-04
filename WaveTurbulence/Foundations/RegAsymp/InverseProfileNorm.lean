/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.InverseProfile

/-! # Weighted local time norm of a coefficient's inverse Fourier profile

DH23 (kqtermsest), time factor: a cutoff inverse Fourier density costs
only its weighted L1 mass. The uncut profile need not be integrable.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

/-- An L1 cutoff times the bounded inverse transform is integrable. -/
theorem integrable_mul_inverseProfile {r : ℕ} {f A : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hA : Integrable A) :
    Integrable (fun t => f t * timeFourier A (-t)) := by
  have hb (t : Fin r → ℝ) : ‖timeFourier A (-t)‖ ≤ ∫ η, ‖A η‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  exact hf.mul_bdd ((timeFourier_continuous hA).comp continuous_neg).aestronglyMeasurable
    (ae_of_all _ hb)

/-- The weighted Fourier bound for the actual cutoff extension. -/
theorem timeFourierNorm_mul_inverseProfile_le {r : ℕ} (θ : ℝ)
    {f A : (Fin r → ℝ) → ℂ} (hf : Integrable f) (hA : Integrable A) (hAm : Measurable A) :
    timeFourierNorm θ (fun t => f t * timeFourier A (-t)) ≤
      ENNReal.ofReal (2 ^ |θ|) * timeFourierNorm θ f *
        (∫⁻ η, timeWeight |θ| η * ‖A η‖ₑ) := by
  have hfg := integrable_mul_inverseProfile hf hA
  rw [timeFourierNorm_eq_lintegral hfg,timeFourierNorm_eq_lintegral hf]
  let K : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|)
  let u := fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ
  let v := fun η => timeWeight |θ| η * ‖A η‖ₑ
  have hu : Measurable u := (timeWeight_measurable θ).mul
    (timeFourier_continuous hf).measurable.enorm
  have hv : Measurable v := (timeWeight_measurable |θ|).mul
    hAm.enorm
  have hpoint (ξ : Fin r → ℝ) : timeWeight θ ξ *
      ‖timeFourier (fun t => f t * timeFourier A (-t)) ξ‖ₑ ≤ ∫⁻ η, K * u (ξ - η) * v η := by
    rw [timeFourier_mul_inverseProfile hf hA]
    calc
      _ ≤ timeWeight θ ξ * ∫⁻ η, ‖timeFourier f (ξ - η) * A η‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
      _ = ∫⁻ η, timeWeight θ ξ *
          (‖timeFourier f (ξ - η)‖ₑ * ‖A η‖ₑ) := by
        have hm : Measurable (fun η => ‖timeFourier f (ξ-η)‖ₑ * ‖A η‖ₑ) :=
          ((timeFourier_continuous hf).measurable.comp
            (measurable_const.sub measurable_id)).enorm.mul hAm.enorm
        simp only [enorm_mul]
        exact (lintegral_const_mul _ hm).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro η
        have hw := timeWeight_add_le_abs θ (ξ - η) η
        rw [sub_add_cancel] at hw
        have hh := mul_le_mul_left hw (‖timeFourier f (ξ - η)‖ₑ * ‖A η‖ₑ)
        simpa only [u, v, K, mul_assoc, mul_left_comm, mul_comm] using hh
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      K * u (p.1 - p.2) * v p.2) :=
    (measurable_const.mul (hu.comp (measurable_fst.sub measurable_snd))).mul
      (hv.comp measurable_snd)
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ η, K * u (ξ - η) * v η := lintegral_mono hpoint
    _ = ∫⁻ η, ∫⁻ ξ, K * u (ξ - η) * v η :=
      lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ η, (K * ∫⁻ ξ, u ξ) * v η := by
      apply lintegral_congr
      intro η
      rw [lintegral_mul_const (f := fun ξ => K * u (ξ - η)) _
        (measurable_const.mul (hu.comp (measurable_id.sub_const η))),
        lintegral_const_mul (f := fun ξ => u (ξ - η)) _ (hu.comp (measurable_id.sub_const η)),
        lintegral_sub_right_eq_self]
    _ = _ := lintegral_const_mul _ hv

end WaveTurbulence.RegAsymp
