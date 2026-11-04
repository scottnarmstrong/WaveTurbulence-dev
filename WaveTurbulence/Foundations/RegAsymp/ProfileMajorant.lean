/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.InverseProfileNorm
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic

/-! # Uniform frequency majorants for the regular-couple remainder

DH23 (remainderbd): the momentum supremum must stay INSIDE the frequency
integral. A genuine measurable majorant supplies this stronger estimate.
The vector index can include root momenta and finitely many derivative words.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

/-- Uniform inverse-profile bound with the pointwise vector supremum inside
Fourier integration, as required by the source norm. -/
theorem mixedFourierNorm00_inverseProfile_le {r : ℕ} {V : Type*} (θ : ℝ)
    {f : (Fin r → ℝ) → ℂ} {A : (Fin r → ℝ) → V → ℂ}
    (hf : Integrable f) (hA : ∀ q, Integrable (fun η => A η q))
    {B : (Fin r → ℝ) → ℝ≥0∞} (hB : Measurable B)
    (hbound : ∀ η q, ‖A η q‖ₑ ≤ B η) :
    mixedFourierNorm00 θ (fun t q => f t * timeFourier (fun η => A η q) (-t)) ≤
      ENNReal.ofReal (2 ^ |θ|) * timeFourierNorm θ f *
        (∫⁻ η, timeWeight |θ| η * B η) := by
  have hfg : ∀ q, Integrable (fun t => f t * timeFourier (fun η => A η q) (-t)) :=
    fun q => integrable_mul_inverseProfile hf (hA q)
  rw [mixedFourierNorm00_eq_lintegral hfg,timeFourierNorm_eq_lintegral hf]
  let K : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|)
  let u := fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ
  let v := fun η => timeWeight |θ| η * B η
  have hu : Measurable u := (timeWeight_measurable θ).mul (timeFourier_continuous hf).measurable.enorm
  have hv : Measurable v := (timeWeight_measurable |θ|).mul hB
  have hpoint (ξ : Fin r → ℝ) (q : V) : timeWeight θ ξ *
      ‖timeFourier (fun t => f t * timeFourier (fun η => A η q) (-t)) ξ‖ₑ ≤
        ∫⁻ η, K * u (ξ-η) * v η := by
    rw [timeFourier_mul_inverseProfile hf (hA q)]
    have hconv : ‖∫ η, timeFourier f (ξ-η) * A η q‖ₑ ≤
        ∫⁻ η, ‖timeFourier f (ξ-η)‖ₑ * B η := by
      apply (enorm_integral_le_lintegral_enorm _).trans
      apply lintegral_mono
      intro η
      dsimp only
      rw [enorm_mul]
      exact mul_le_mul_right (hbound η q) _
    calc
      _ ≤ timeWeight θ ξ * ∫⁻ η, ‖timeFourier f (ξ-η)‖ₑ * B η := mul_le_mul_right hconv _
      _ = ∫⁻ η, timeWeight θ ξ * (‖timeFourier f (ξ-η)‖ₑ * B η) := by
        have hm : Measurable (fun η => ‖timeFourier f (ξ-η)‖ₑ * B η) :=
          ((timeFourier_continuous hf).measurable.comp
            (measurable_const.sub measurable_id)).enorm.mul hB
        exact (lintegral_const_mul _ hm).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro η
        have hw := timeWeight_add_le_abs θ (ξ-η) η
        rw [sub_add_cancel] at hw
        have h := mul_le_mul_left hw (‖timeFourier f (ξ-η)‖ₑ * B η)
        simpa only [u,v,K,mul_assoc,mul_left_comm,mul_comm] using h
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      K * u (p.1 - p.2) * v p.2) :=
    (measurable_const.mul (hu.comp (measurable_fst.sub measurable_snd))).mul
      (hv.comp measurable_snd)
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ η, K * u (ξ - η) * v η := by
      apply lintegral_mono
      intro ξ
      change timeWeight θ ξ * (⨆ q, ‖timeFourier (fun t => f t * timeFourier (fun η => A η q) (-t)) ξ‖ₑ) ≤ _
      rw [ENNReal.mul_iSup]
      exact iSup_le (fun q => hpoint ξ q)
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
