/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ScalarFourierTranslation
public import WaveTurbulence.Foundations.Sumint.ScalarPowerKernel
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication

/-!
# Scalar bracket-weighted Fourier mass and the native one-time norm

The integer bracket weight one controls every multiplier regularity
used here. Smooth compact scalar profiles have finite mass, and products
are bounded by the landed one-time Fourier product estimate.
-/

public section
open MeasureTheory ENNReal
open scoped FourierTransform ContDiff
namespace WaveTurbulence.Sumint

/-- The scalar Fourier L1 mass with one Japanese-bracket weight. -/
@[expose] noncomputable def scalarFourierMass (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ, ENNReal.ofReal (scalarBracket ξ)*‖𝓕 f ξ‖ₑ

/-- The native one-time Fourier transform is exactly the ordinary scalar transform. -/
theorem timeFourier_scalar_lift (f : ℝ → ℂ) (ξ : Fin 1 → ℝ) :
    Fourier.timeFourier (fun t : Fin 1 → ℝ => f (t 0)) ξ = 𝓕 f (ξ 0) := by
  have he := Fourier.timeFourier_coordinate_product (fun _ : Fin 1 => f) ξ
  simpa only [Fin.prod_univ_one] using he

/-- In one native coordinate the maximum bracket is exactly the scalar bracket. -/
theorem timeBracket_one_eq (ξ : Fin 1 → ℝ) : Fourier.timeBracket ξ = scalarBracket (ξ 0) := by
  apply le_antisymm
  · apply Fourier.timeBracket_le (one_le_scalarBracket _)
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact le_rfl
  · exact Fourier.bracket_le_timeBracket ξ 0

/-- The exact native one-time weighted norm equals scalar Fourier mass for a genuinely integrable coefficient. -/
theorem timeFourierNorm_scalar_lift (f : ℝ → ℂ) (hf : Integrable f) :
    Fourier.timeFourierNorm 1 (fun t : Fin 1 → ℝ => f (t 0)) = scalarFourierMass f := by
  have hi : Integrable (fun t : Fin 1 → ℝ => f (t 0)) :=
    (volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_of_integrable hf
  rw [Fourier.timeFourierNorm_eq_lintegral hi]
  simp_rw [timeFourier_scalar_lift,Fourier.timeWeight,timeBracket_one_eq,Real.rpow_one]
  exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (fun ξ : ℝ => ENNReal.ofReal (scalarBracket ξ)*‖𝓕 f ξ‖ₑ)

/-- Smooth compact scalar cutoffs have finite weighted Fourier mass. -/
theorem scalarFourierMass_lt_top_of_smooth_compact {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) : scalarFourierMass f < ⊤ := by
  have hfl : HasCompactSupport (fun t : Fin 1 → ℝ => f (t 0)) :=
    hf.comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)
  have hproj : ContDiff ℝ ∞ (fun t : Fin 1 → ℝ => t 0) := by fun_prop
  have hsl : ContDiff ℝ ∞ (fun t : Fin 1 → ℝ => f (t 0)) := hs.comp hproj
  rw [← timeFourierNorm_scalar_lift f (hs.continuous.integrable_of_hasCompactSupport hf)]
  exact Fourier.timeFourierNorm_lt_top_of_smooth_compact 1 hfl hsl

end WaveTurbulence.Sumint
