/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeBasic
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
import Mathlib.Tactic

/-!
# Products and convolution for time Fourier norms

The Fourier transform of a product is the convolution of the transforms.
The regularity hypothesis selects the continuous representative used in
Fourier inversion; the norm estimates apply to finite weighted Fourier norms.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

private theorem pairing_continuous (r : ℕ) :
    Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => timePairing r p.1 p.2) := by
  change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
  fun_prop

private theorem pairing_comm {r : ℕ} (x y : Fin r → ℝ) :
    timePairing r x y = timePairing r y x := by
  change x ⬝ᵥ y = y ⬝ᵥ x
  exact dotProduct_comm _ _

/-- Product-to-convolution identity. One factor needs Fourier inversion;
ordinary continuity and integrability are sufficient for that step. -/
theorem timeFourier_mul_eq {r : ℕ} {f g : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hhg : Integrable (timeFourier g))
    (hgc : Continuous g) (ξ : Fin r → ℝ) :
    timeFourier (fun t => f t * g t) ξ =
      ∫ η, timeFourier f (ξ - η) * timeFourier g η := by
  let fξ := fun t => Real.fourierChar (-timePairing r t ξ) • f t
  have hfξ : Integrable fξ :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (pairing_continuous r) ξ).mpr hf
  have hd := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := -(timePairing r)) (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
    (by exact (pairing_continuous r).neg) hfξ hhg
  have hl (η : Fin r → ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (-(timePairing r)) fξ η =
        timeFourier f (ξ - η) := by
    unfold VectorFourier.fourierIntegral timeFourier
    simp only [LinearMap.neg_apply, neg_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp [fξ]
      rw [← mul_smul, ← AddChar.map_add_eq_mul]
      have he : timePairing r t η + -timePairing r t ξ = -timePairing r t (ξ - η) := by
        rw [map_sub]
        ring
      rw [he]
  have hr (t : Fin r → ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (-(timePairing r)).flip
        (timeFourier g) t = g t := by
    rw [← timeFourier_inversion hg hhg hgc t]
    change (∫ η, Real.fourierChar (-((-(timePairing r)).flip η t)) • timeFourier g η) =
      ∫ η, Real.fourierChar (-timePairing r η (-t)) • timeFourier g η
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, map_neg, neg_neg, pairing_comm t]

  simp_rw [hl, hr] at hd
  change (∫ η, timeFourier f (ξ - η) * timeFourier g η) = ∫ t, fξ t * g t at hd
  rw [hd]
  change (∫ t, Real.fourierChar (-timePairing r t ξ) • (f t * g t)) =
    ∫ t, fξ t * g t
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [fξ, Circle.smul_def, mul_assoc]

/-- Finite weighted norms have integrable original time slices. -/
theorem integrable_of_timeFourierNorm_lt_top {r : ℕ} {θ : ℝ}
    {f : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤) : Integrable f := by
  by_contra h
  rw [timeFourierNorm_of_not_integrable h] at hf
  exact (lt_irrefl _ hf)

/-- At nonnegative regularity, finite weighted norms also give Fourier-L¹
integrability, as required for inversion and convolution. -/
theorem integrable_timeFourier_of_norm_lt_top {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    {f : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤) : Integrable (timeFourier f) := by
  have hfi := integrable_of_timeFourierNorm_lt_top hf
  rw [timeFourierNorm_eq_lintegral hfi] at hf
  refine ⟨(timeFourier_continuous hfi).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt _ hf
  apply lintegral_mono
  intro ξ
  have hw : (1 : ℝ≥0∞) ≤ timeWeight θ ξ := by
    simpa only [timeWeight, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)
  simpa only [one_mul] using mul_le_mul_left hw ‖timeFourier f ξ‖ₑ

/-- Banach-algebra estimate on continuous representatives with finite norms.
The loss is the explicit constant `2^θ`, independent of the number of time
variables. Finiteness is the usual membership condition for this algebra. -/
theorem timeFourierNorm_mul_asymmetric_le {r : ℕ} (θ : ℝ)
    {f g : (Fin r → ℝ) → ℂ} (hgc : Continuous g)
    (hfn : timeFourierNorm θ f < ⊤) (hgn : timeFourierNorm |θ| g < ⊤) :
    timeFourierNorm θ (fun t => f t * g t) ≤
      ENNReal.ofReal (2 ^ |θ|) * timeFourierNorm θ f * timeFourierNorm |θ| g := by
  have hf := integrable_of_timeFourierNorm_lt_top hfn
  have hg := integrable_of_timeFourierNorm_lt_top hgn
  have hhg := integrable_timeFourier_of_norm_lt_top (abs_nonneg θ) hgn
  have hgb (t : Fin r → ℝ) : ‖g t‖ ≤ ∫ η, ‖timeFourier g η‖ := by
    rw [← timeFourier_inversion hg hhg hgc t]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hfg := hf.mul_bdd hgc.aestronglyMeasurable (ae_of_all _ hgb)
  rw [timeFourierNorm_eq_lintegral hfg, timeFourierNorm_eq_lintegral hf,
    timeFourierNorm_eq_lintegral hg]
  let K : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|)
  let u := fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ
  let v := fun η => timeWeight |θ| η * ‖timeFourier g η‖ₑ
  have hu : Measurable u := (timeWeight_measurable θ).mul
    (timeFourier_continuous hf).measurable.enorm
  have hv : Measurable v := (timeWeight_measurable |θ|).mul
    (timeFourier_continuous hg).measurable.enorm
  have hpoint (ξ : Fin r → ℝ) : timeWeight θ ξ *
      ‖timeFourier (fun t => f t * g t) ξ‖ₑ ≤ ∫⁻ η, K * u (ξ - η) * v η := by
    rw [timeFourier_mul_eq hf hg hhg hgc]
    calc
      _ ≤ timeWeight θ ξ * ∫⁻ η, ‖timeFourier f (ξ - η) * timeFourier g η‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
      _ = ∫⁻ η, timeWeight θ ξ *
          (‖timeFourier f (ξ - η)‖ₑ * ‖timeFourier g η‖ₑ) := by
        rw [lintegral_const_mul _ (by fun_prop)]
        simp only [enorm_mul]
      _ ≤ _ := by
        apply lintegral_mono
        intro η
        have hw := timeWeight_add_le_abs θ (ξ - η) η
        rw [sub_add_cancel] at hw
        have hh := mul_le_mul_left hw (‖timeFourier f (ξ - η)‖ₑ * ‖timeFourier g η‖ₑ)
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

/-- Banach-algebra estimate at nonnegative regularity. -/
theorem timeFourierNorm_mul_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    {f g : (Fin r → ℝ) → ℂ} (hgc : Continuous g)
    (hfn : timeFourierNorm θ f < ⊤) (hgn : timeFourierNorm θ g < ⊤) :
    timeFourierNorm θ (fun t => f t * g t) ≤
      ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ f * timeFourierNorm θ g := by
  simpa only [abs_of_nonneg hθ] using
    timeFourierNorm_mul_asymmetric_le θ hgc hfn (by simpa only [abs_of_nonneg hθ] using hgn)

end WaveTurbulence.Fourier
