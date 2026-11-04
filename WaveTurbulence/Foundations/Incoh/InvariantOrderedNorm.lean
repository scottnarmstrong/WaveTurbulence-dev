/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.InvariantProductBounds
public import WaveTurbulence.Foundations.Incoh.GeneralThreeMomentNorm
public import WaveTurbulence.Foundations.Fourier.CutoffEightMoments
public import WaveTurbulence.Foundations.Fourier.ThreeMomentNorm
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Quarter regularity from coordinate first variation

The landed eight-moment and joint-frequency estimates apply directly to
balanced phase amplitudes with translation-invariant ordering weights.
Only first scalar variation is needed in each selected clock.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Explicit bound using the actual coordinate-factor mass and first variation.
This generic inequality is instantiated below with the literal localized windows. -/
theorem mixedFourierNorm00_invariantOrdered_le {n : ℕ} {V : Type*} {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (h : Fourier.CutoffControl χ)
    (f : V → Fin (n + 2) → ℝ → ℝ) (hf : ∀ k j, ContDiff ℝ ∞ (f k j))
    (phase : V → Fin (n + 2) → ℝ) (hp : ∀ k, ∑ j, phase k j = 0)
    (H : V → (Fin (n + 2) → ℝ) → ℂ) (hHd : ∀ k, ContDiff ℝ ∞ (H k))
    (hH : ∀ k v, ‖H k v‖ ≤ 1) (hshift : ∀ k v c, H k (fun j => v j + c) = H k v)
    {B : ℝ≥0∞}
    (hm : ∀ k j, (∫⁻ x in Icc (-h.radius) h.radius, ENNReal.ofReal ‖f k j x‖) ≤ B)
    (hdm : ∀ k j, (∫⁻ x in Icc (-h.radius) h.radius, ENNReal.ofReal ‖deriv (f k j) x‖) ≤ B) :
    Fourier.mixedFourierNorm00 (1 / 4) (fun t k => Fourier.weightedOrderedIntegral (n + 2) χ χ
      (invariantProductAmplitude (f k) (phase k) (H k)) t) ≤
      ENNReal.ofReal (8 * Fourier.jointFrequencyConstant) *
        (Fourier.orderedFourMomentFactor h.radius h.bound * ((3 + (n + 2 : ℕ) : ℝ≥0∞) * B ^ (n + 2))) := by
  let A := fun k => invariantProductAmplitude (f k) (phase k) (H k)
  have hA (k : V) : ContDiff ℝ ∞ (A k) :=
    contDiff_invariantProductAmplitude (hf k) (phase k) (hHd k)
  have hOut (k : V) : ContDiff ℝ ∞ (Fourier.weightedOrderedIntegral (n + 2) χ χ (A k)) :=
    Fourier.weightedOrderedIntegral_contDiff hχ hχ (hA k)
  have hcOut (k : V) : HasCompactSupport (Fourier.weightedOrderedIntegral (n + 2) χ χ (A k)) :=
    Fourier.weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds _
  have hMom (k : V) : ENNReal.ofReal (Fourier.threeTimeMomentSum
      (Fourier.weightedOrderedIntegral (n + 2) χ χ (A k))) ≤
      Fourier.orderedFourMomentFactor h.radius h.bound * ((3 + (n + 2 : ℕ) : ℝ≥0∞) * B ^ (n + 2)) := by
    apply (Fourier.threeTimeMomentSum_weighted_cutoff_le hχ (hA k) h).trans
    apply mul_le_mul' le_rfl
    have h0 := boxIntegral_invariantProductAmplitude_le (fun j => (hf k j).continuous) (phase k) (hH k) h.radius (hm k)
    have h1 := boxIntegral_diagonal_invariantProductAmplitude_le (hf k) (hp k) (hHd k)
      (hH k) (hshift k) h.radius (hm k) (hdm k)
    exact (add_le_add (mul_le_mul' le_rfl h0) h1).trans_eq (by ring)
  exact mixedFourierNorm00_le_threeMoment_bound hOut hcOut hMom

end WaveTurbulence.Incoh
