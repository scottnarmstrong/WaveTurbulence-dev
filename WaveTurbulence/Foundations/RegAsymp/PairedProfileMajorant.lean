/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRegularity
public import WaveTurbulence.Foundations.RegAsymp.PairedFrequencyWeight
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic

/-! # The source π-normalized profile controls the genuine mixed time norm

The momentum/derivative supremum stays inside the time-frequency
integral. A single measurable λ-envelope is sufficient, with ae bounds.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier ClassJR
open scoped ENNReal

/-- Uniform inverse-profile estimate in the original source λ measure. -/
theorem mixedFourierNorm00_pairedProfile_le {V : Type*} {η : ℝ} (hη : 0 ≤ η)
    {f : (Fin 2 → ℝ) → ℂ} {A : (ℝ × ℝ) → V → ℂ}
    (hf : Integrable f) (hA : ∀ q, Integrable (fun lam => A lam q))
    {B : (ℝ × ℝ) → ℝ≥0∞} (hB : Measurable B)
    (hbound : ∀ q, ∀ᵐ lam : ℝ × ℝ, ‖A lam q‖ₑ ≤ B lam) :
    mixedFourierNorm00 η (fun t q => f t*pairedInverseProfile (fun lam => A lam q) t) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η f*(∫⁻ lam, wL η lam*B lam) := by
  have hfg (q : V) : Integrable (fun t => f t*pairedInverseProfile (fun lam => A lam q) t) :=
    integrable_mul_pairedInverseProfile hf (hA q)
  rw [mixedFourierNorm00_eq_lintegral hfg,timeFourierNorm_eq_lintegral hf]
  let K : ℝ≥0∞ := ENNReal.ofReal (2^η)
  let u := fun ξ => timeWeight η ξ*‖timeFourier f ξ‖ₑ
  let v := fun lam => wL η lam*B lam
  have hu : Measurable u := (timeWeight_measurable η).mul (timeFourier_continuous hf).measurable.enorm
  have hv : Measurable v := (measurable_wL η).mul hB
  have hpoint (ξ : Fin 2 → ℝ) (q : V) : timeWeight η ξ*
      ‖timeFourier (fun t => f t*pairedInverseProfile (fun lam => A lam q) t) ξ‖ₑ ≤
        ∫⁻ lam, K*u (ξ-pairedTimeFrequency lam)*v lam := by
    simp only [pairedInverseProfile]
    rw [timeFourier_mul_pairedProfile hf (hA q)]
    have hc : ‖∫ lam, timeFourier f (ξ-pairedTimeFrequency lam)*A lam q‖ₑ ≤
        ∫⁻ lam, ‖timeFourier f (ξ-pairedTimeFrequency lam)‖ₑ*B lam := by
      apply (enorm_integral_le_lintegral_enorm _).trans
      apply lintegral_mono_ae
      filter_upwards [hbound q] with lam hlam
      rw [enorm_mul]
      exact mul_le_mul' le_rfl hlam
    calc
      _ ≤ timeWeight η ξ*∫⁻ lam, ‖timeFourier f (ξ-pairedTimeFrequency lam)‖ₑ*B lam :=
        mul_le_mul' le_rfl hc
      _ = ∫⁻ lam, timeWeight η ξ*(‖timeFourier f (ξ-pairedTimeFrequency lam)‖ₑ*B lam) := by
        have hm : Measurable (fun lam => ‖timeFourier f (ξ-pairedTimeFrequency lam)‖ₑ*B lam) :=
          ((timeFourier_continuous hf).measurable.comp
          (measurable_const.sub continuous_pairedTimeFrequency.measurable)).enorm.mul hB
        exact (lintegral_const_mul _ hm).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro lam
        have hw := timeWeight_add_le_abs η (ξ-pairedTimeFrequency lam) (pairedTimeFrequency lam)
        rw [sub_add_cancel,abs_of_nonneg hη] at hw
        have hw' := hw.trans (mul_le_mul' le_rfl (timeWeight_pairedTimeFrequency_le hη lam))
        have hh := mul_le_mul' hw' (le_refl (‖timeFourier f (ξ-pairedTimeFrequency lam)‖ₑ*B lam))
        simpa only [K,u,v,mul_assoc,mul_left_comm,mul_comm] using hh
  have hj : Measurable (fun p : (Fin 2 → ℝ) × (ℝ × ℝ) =>
      K*u (p.1-pairedTimeFrequency p.2)*v p.2) :=
    (measurable_const.mul (hu.comp (measurable_fst.sub
      (continuous_pairedTimeFrequency.measurable.comp measurable_snd)))).mul (hv.comp measurable_snd)
  calc
    _ ≤ ∫⁻ ξ : Fin 2 → ℝ, ∫⁻ lam : ℝ × ℝ, K*u (ξ-pairedTimeFrequency lam)*v lam := by
      apply lintegral_mono
      intro ξ
      change timeWeight η ξ*(⨆ q, ‖timeFourier
        (fun t => f t*pairedInverseProfile (fun lam => A lam q) t) ξ‖ₑ) ≤ _
      rw [ENNReal.mul_iSup]
      exact iSup_le (fun q => hpoint ξ q)
    _ = ∫⁻ lam : ℝ × ℝ, ∫⁻ ξ : Fin 2 → ℝ, K*u (ξ-pairedTimeFrequency lam)*v lam :=
      lintegral_lintegral_swap hj.aemeasurable
    _ = ∫⁻ lam : ℝ × ℝ, (K*∫⁻ ξ, u ξ)*v lam := by
      apply lintegral_congr
      intro lam
      rw [lintegral_mul_const (f := fun ξ => K*u (ξ-pairedTimeFrequency lam)) _
        (measurable_const.mul (hu.comp (measurable_id.sub_const (pairedTimeFrequency lam)))),
        lintegral_const_mul (f := fun ξ => u (ξ-pairedTimeFrequency lam)) _
          (hu.comp (measurable_id.sub_const (pairedTimeFrequency lam))),lintegral_sub_right_eq_self]
    _ = _ := lintegral_const_mul _ hv

end WaveTurbulence.RegAsymp
