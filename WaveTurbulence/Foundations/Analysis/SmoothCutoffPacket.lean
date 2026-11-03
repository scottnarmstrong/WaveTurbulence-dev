/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.SpectralPacket

/-!
# A smooth cutoff as a spectral packet

The leaf of the spectral tree is the actual Fourier transform of the
fixed smooth compactly supported cutoff. Its certificate follows from
two integrations by parts and Fourier inversion.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform ContDiff

namespace WaveTurbulence.Analysis

/-- The Fourier transform of a smooth compactly supported cutoff is integrable. -/
theorem integrable_fourier_cutoff {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : Integrable (𝓕 χ) := by
  have hi := hχ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
  apply (integrable_cauchyWeight.const_mul (cutoffFourierConstant χ)).mono'
    (continuous_fourier_of_integrable hi).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_fourier_cutoff_le hχ hs)

/-- The initial packet used at an unbranched leaf. -/
@[expose] noncomputable def smoothCutoffPacket {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) : SpectralPacket where
  Index := Unit
  fintypeIndex := inferInstance
  centre := fun _ => 0
  weight := fun _ => ENNReal.ofReal (cutoffFourierConstant χ)
  density := 𝓕 χ
  integrable_density := integrable_fourier_cutoff hχ hs
  bound t := by
    have hh := ENNReal.ofReal_le_ofReal (norm_fourier_cutoff_le hχ hs t)
    simpa only [frequencyEnvelope, Fintype.sum_unique, sub_zero, ofReal_norm,
      ENNReal.ofReal_mul (cutoffFourierConstant_nonneg χ)] using hh

/-- The leaf packet synthesizes to the cutoff itself. -/
theorem synthesis_smoothCutoffPacket {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (t : ℝ) :
    (smoothCutoffPacket hχ hs).synthesis t = χ t := by
  have hi := hχ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
  exact hi.fourierInv_fourier_eq (integrable_fourier_cutoff hχ hs) hχ.continuous.continuousAt

end WaveTurbulence.Analysis
