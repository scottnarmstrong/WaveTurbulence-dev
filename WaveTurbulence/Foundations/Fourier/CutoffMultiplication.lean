/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm
public import WaveTurbulence.Foundations.Fourier.Chi0
import Mathlib.Tactic

/-!
# Multiplication by smooth cutoffs

TARGET `(normX1)`: a smooth compactly supported multiplier acts boundedly
at every real time regularity exponent, including negative exponents.
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Fourier

/-- The explicit Fourier-weight expression controlling a cutoff multiplier. -/
@[expose] noncomputable def cutoffMultiplierConstant {r : ℕ} (θ : ℝ)
    (κ : (Fin r → ℝ) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ |θ|) * timeFourierNorm |θ| κ

/-- The multiplier constant is finite for every smooth compactly supported
cutoff. It depends on the cutoff and regularity exponent, not on the input. -/
theorem cutoffMultiplierConstant_lt_top {r : ℕ} (θ : ℝ)
    {κ : (Fin r → ℝ) → ℂ} (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    cutoffMultiplierConstant θ κ < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (timeFourierNorm_lt_top_of_smooth_compact |θ| hκ hs)

/-- Bounded multiplication by smooth compactly supported cutoffs at every
real regularity exponent. The input is an arbitrary integrable function
with finite weighted Fourier norm. -/
theorem timeFourierNorm_mul_cutoff_le {r : ℕ} (θ : ℝ)
    {f κ : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤)
    (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    timeFourierNorm θ (fun t => f t * κ t) ≤
      cutoffMultiplierConstant θ κ * timeFourierNorm θ f := by
  have h := timeFourierNorm_mul_asymmetric_le θ hs.continuous hf
    (timeFourierNorm_lt_top_of_smooth_compact |θ| hκ hs)
  simpa only [cutoffMultiplierConstant, mul_assoc, mul_left_comm, mul_comm] using h

/-- Multiplication preserves finiteness of the weighted norm. -/
theorem timeFourierNorm_mul_cutoff_lt_top {r : ℕ} (θ : ℝ)
    {f κ : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤)
    (hκ : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ) :
    timeFourierNorm θ (fun t => f t * κ t) < ⊤ :=
  (timeFourierNorm_mul_cutoff_le θ hf hκ hs).trans_lt
    (ENNReal.mul_lt_top (cutoffMultiplierConstant_lt_top θ hκ hs) hf)

/-- The tensor cutoff as a complex multiplier. -/
@[expose] noncomputable def chi0TensorComplex {r : ℕ} (t : Fin r → ℝ) : ℂ := chi0Tensor t

theorem chi0TensorComplex_hasCompactSupport (r : ℕ) :
    HasCompactSupport (chi0TensorComplex (r := r)) :=
  (chi0Tensor_hasCompactSupport r).comp_left Complex.ofReal_zero

@[fun_prop] theorem chi0TensorComplex_contDiff {r : ℕ} :
    ContDiff ℝ ∞ (chi0TensorComplex (r := r)) := by
  unfold chi0TensorComplex
  exact Complex.ofRealCLM.contDiff.comp chi0Tensor_contDiff

/-- The fixed tensor cutoff of TARGET L623 acts boundedly on every
weighted time Fourier norm. -/
theorem timeFourierNorm_mul_chi0_le {r : ℕ} (θ : ℝ)
    {f : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤) :
    timeFourierNorm θ (fun t => f t * chi0TensorComplex t) ≤
      cutoffMultiplierConstant θ (chi0TensorComplex (r := r)) * timeFourierNorm θ f :=
  timeFourierNorm_mul_cutoff_le θ hf (chi0TensorComplex_hasCompactSupport r)
    chi0TensorComplex_contDiff

end WaveTurbulence.Fourier
