/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeProduct

/-! # Cutoff inverse Fourier profiles in the regular asymptotics

DH23 (maincoef1): after integrating coefficient variables, the time factor
is an inverse Fourier integral of an L1 density. Multiplication by a smooth
cutoff gives a genuine local Fourier-norm extension. No integrability of
the uncut inverse transform is assumed.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

private theorem pairing_continuous (r : ℕ) :
    Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => timePairing r p.1 p.2) := by
  change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
  fun_prop

private theorem pairing_comm {r : ℕ} (x y : Fin r → ℝ) :
    timePairing r x y = timePairing r y x := by
  change x ⬝ᵥ y = y ⬝ᵥ x
  exact dotProduct_comm _ _

/-- Multiplication by an inverse Fourier profile is convolution with its
actual density. This needs neither a second Fourier inversion assumption
nor integrability of the uncut profile. -/
theorem timeFourier_mul_inverseProfile {r : ℕ} {f A : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hA : Integrable A) (ξ : Fin r → ℝ) :
    timeFourier (fun t => f t * timeFourier A (-t)) ξ =
      ∫ η, timeFourier f (ξ - η) * A η := by
  let fξ := fun t => Real.fourierChar (-timePairing r t ξ) • f t
  have hfξ : Integrable fξ :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (pairing_continuous r) ξ).mpr hf
  have hd := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := -(timePairing r)) (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
    (by exact (pairing_continuous r).neg) hfξ hA
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
      VectorFourier.fourierIntegral Real.fourierChar volume (-(timePairing r)).flip A t =
        timeFourier A (-t) := by
    change (∫ η, Real.fourierChar (-((-(timePairing r)).flip η t)) • A η) =
      ∫ η, Real.fourierChar (-timePairing r η (-t)) • A η
    simp only [LinearMap.flip_apply,LinearMap.neg_apply,map_neg,neg_neg,pairing_comm t]

  simp_rw [hl, hr] at hd
  change (∫ η, timeFourier f (ξ - η) * A η) = ∫ t, fξ t * timeFourier A (-t) at hd
  rw [hd]
  change (∫ t, Real.fourierChar (-timePairing r t ξ) • (f t * timeFourier A (-t))) =
    ∫ t, fξ t * timeFourier A (-t)
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [fξ, Circle.smul_def, mul_assoc]


end WaveTurbulence.RegAsymp
