/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import WaveTurbulence.Foundations.Fourier.TimeProduct

/-!
# Products in the general-variable order-zero mixed norm

TARGET L581, L589. The vector supremum remains inside the frequency integral.
Fourier envelopes are measurable even for arbitrary uncountable vector
index types, because their scalar slices are continuous in frequency.
-/

public section

namespace WaveTurbulence.Fourier
open MeasureTheory
open scoped ENNReal

/-- The asymmetric product estimate holds at every real time regularity. -/
theorem mixedFourierNorm00_mul_asymmetric_le {r : ℕ} {V : Type*} (θ : ℝ)
    {F G : (Fin r → ℝ) → V → ℂ} (hGc : ∀ v, Continuous (fun t => G t v))
    (hFn : mixedFourierNorm00 θ F < ⊤) (hGn : mixedFourierNorm00 |θ| G < ⊤) :
    mixedFourierNorm00 θ (fun t v => F t v * G t v) ≤
      ENNReal.ofReal (2 ^ |θ|) * mixedFourierNorm00 θ F * mixedFourierNorm00 |θ| G := by
  have hf := integrable_of_mixedFourierNorm00_lt_top hFn
  have hg := integrable_of_mixedFourierNorm00_lt_top hGn
  have hgg (v : V) : Integrable (timeFourier (fun t => G t v)) :=
    integrable_timeFourier_of_norm_lt_top (abs_nonneg θ)
      ((timeFourierNorm_slice_le_mixedFourierNorm00 |θ| G v).trans_lt hGn)
  have hfg (v : V) : Integrable (fun t => F t v * G t v) := by
    have hb (t : Fin r → ℝ) : ‖G t v‖ ≤ ∫ η, ‖timeFourier (fun t => G t v) η‖ := by
      rw [← timeFourier_inversion (hg v) (hgg v) (hGc v) t]
      exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    exact (hf v).mul_bdd (hGc v).aestronglyMeasurable (ae_of_all _ hb)
  rw [mixedFourierNorm00_eq_lintegral hfg, mixedFourierNorm00_eq_lintegral hf,
    mixedFourierNorm00_eq_lintegral hg]
  let K : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|)
  let u := fun ξ => timeWeight θ ξ * mixedFourierEnvelope00 F ξ
  let v := fun η => timeWeight |θ| η * mixedFourierEnvelope00 G η
  have hu : Measurable u := (timeWeight_measurable θ).mul (measurable_mixedFourierEnvelope00 hf)
  have hv : Measurable v := (timeWeight_measurable |θ|).mul (measurable_mixedFourierEnvelope00 hg)
  have hpoint (ξ : Fin r → ℝ) : timeWeight θ ξ *
      mixedFourierEnvelope00 (fun t v => F t v * G t v) ξ ≤ ∫⁻ η, K * u (ξ - η) * v η := by
    unfold mixedFourierEnvelope00
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro w
    rw [timeFourier_mul_eq (hf w) (hg w) (hgg w) (hGc w)]
    calc
      _ ≤ timeWeight θ ξ * ∫⁻ η,
          ‖timeFourier (fun t => F t w) (ξ - η) * timeFourier (fun t => G t w) η‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
      _ ≤ timeWeight θ ξ * ∫⁻ η, mixedFourierEnvelope00 F (ξ - η) * mixedFourierEnvelope00 G η := by
        apply mul_le_mul_right
        apply lintegral_mono
        intro η
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul'
          (le_iSup (fun v : V => ‖timeFourier (fun t => F t v) (ξ - η)‖ₑ) w)
          (le_iSup (fun v : V => ‖timeFourier (fun t => G t v) η‖ₑ) w)
      _ = ∫⁻ η, timeWeight θ ξ * (mixedFourierEnvelope00 F (ξ - η) * mixedFourierEnvelope00 G η) := by
        have hm : Measurable (fun η => mixedFourierEnvelope00 F (ξ - η) * mixedFourierEnvelope00 G η) :=
          ((measurable_mixedFourierEnvelope00 hf).comp
            (measurable_const.sub measurable_id)).mul (measurable_mixedFourierEnvelope00 hg)
        exact (lintegral_const_mul _ hm).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro η
        have hw := timeWeight_add_le_abs θ (ξ - η) η
        rw [sub_add_cancel] at hw
        have hh := mul_le_mul_left hw (mixedFourierEnvelope00 F (ξ - η) * mixedFourierEnvelope00 G η)
        simpa only [u, v, K, mul_assoc, mul_left_comm, mul_comm] using hh
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      K * u (p.1 - p.2) * v p.2) :=
    (measurable_const.mul (hu.comp (measurable_fst.sub measurable_snd))).mul (hv.comp measurable_snd)
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ η, K * u (ξ - η) * v η := lintegral_mono hpoint
    _ = ∫⁻ η, ∫⁻ ξ, K * u (ξ - η) * v η := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ η, (K * ∫⁻ ξ, u ξ) * v η := by
      apply lintegral_congr
      intro η
      rw [lintegral_mul_const (f := fun ξ => K * u (ξ - η)) _
        (measurable_const.mul (hu.comp (measurable_id.sub_const η))),
        lintegral_const_mul (f := fun ξ => u (ξ - η)) _ (hu.comp (measurable_id.sub_const η)),
        lintegral_sub_right_eq_self]
    _ = _ := lintegral_const_mul _ hv

/-- At nonnegative regularity, the same norm controls both product factors. -/
theorem mixedFourierNorm00_mul_le {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    {F G : (Fin r → ℝ) → V → ℂ} (hGc : ∀ v, Continuous (fun t => G t v))
    (hFn : mixedFourierNorm00 θ F < ⊤) (hGn : mixedFourierNorm00 θ G < ⊤) :
    mixedFourierNorm00 θ (fun t v => F t v * G t v) ≤
      ENNReal.ofReal (2 ^ θ) * mixedFourierNorm00 θ F * mixedFourierNorm00 θ G := by
  simpa only [abs_of_nonneg hθ] using
    mixedFourierNorm00_mul_asymmetric_le θ hGc hFn (by simpa only [abs_of_nonneg hθ] using hGn)

end WaveTurbulence.Fourier
