/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoordinateFactorMass

/-!
# Phase-independent box bounds for invariant product amplitudes

The ordering weight has modulus at most one and is invariant under a
common clock shift. Balanced temporal phases disappear from the only
amplitude derivative used in the landed eight-moment estimate.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Unit ordering weights and real phases do not increase the product amplitude. -/
theorem norm_invariantProductAmplitude_le {m : ℕ} (f : Fin m → ℝ → ℝ)
    (phase : Fin m → ℝ) {H : (Fin m → ℝ) → ℂ} (hH : ∀ v, ‖H v‖ ≤ 1) (v : Fin m → ℝ) :
    ‖invariantProductAmplitude f phase H v‖ ≤ ‖coordinateFactorProduct f v‖ := by
  rw [invariantProductAmplitude, norm_mul, norm_mul, Fourier.norm_linearTimePhase, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (hH v)

/-- The common-clock derivative costs only the coordinate-factor first variation. -/
theorem norm_diagonal_invariantProductAmplitude_le {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) {phase : Fin m → ℝ} (hphase : ∑ j, phase j = 0)
    {H : (Fin m → ℝ) → ℂ} (hHd : ContDiff ℝ ∞ H) (hH : ∀ v, ‖H v‖ ≤ 1)
    (hshift : ∀ v c, H (fun j => v j + c) = H v) (v : Fin m → ℝ) :
    ‖Fourier.timeDirectionalDerivative (fun _ => 1) (invariantProductAmplitude f phase H) v‖ ≤
      ‖coordinateFactorDiagonal f v‖ := by
  rw [timeDirectionalDerivative_invariantProductAmplitude hf hphase hHd hshift,
    norm_mul, norm_mul, Fourier.norm_linearTimePhase, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (hH v)

/-- The amplitude box integral is bounded by the common scalar mass product. -/
theorem boxIntegral_invariantProductAmplitude_le {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, Continuous (f j)) (phase : Fin m → ℝ)
    {H : (Fin m → ℝ) → ℂ} (hH : ∀ v, ‖H v‖ ≤ 1) {B : ℝ≥0∞} (R : ℝ)
    (hm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖f i x‖) ≤ B) :
    Fourier.boxIntegral m (fun v => ‖invariantProductAmplitude f phase H v‖ₑ) R ≤ B ^ m := by
  apply le_trans ?_ (boxIntegral_coordinateFactorProduct_le hf R hm)
  apply Fourier.boxIntegral_mono m
  intro v
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (norm_invariantProductAmplitude_le f phase hH v)

/-- The diagonal amplitude box integral uses only first scalar derivatives. -/
theorem boxIntegral_diagonal_invariantProductAmplitude_le {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) {phase : Fin m → ℝ} (hphase : ∑ j, phase j = 0)
    {H : (Fin m → ℝ) → ℂ} (hHd : ContDiff ℝ ∞ H) (hH : ∀ v, ‖H v‖ ≤ 1)
    (hshift : ∀ v c, H (fun j => v j + c) = H v) {B : ℝ≥0∞} (R : ℝ)
    (hm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖f i x‖) ≤ B)
    (hdm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖deriv (f i) x‖) ≤ B) :
    Fourier.boxIntegral m
      (fun v => ‖Fourier.timeDirectionalDerivative (fun _ => 1) (invariantProductAmplitude f phase H) v‖ₑ) R ≤
        (m : ℝ≥0∞) * B ^ m := by
  apply le_trans ?_ (boxIntegral_coordinateFactorDiagonal_le hf R hm hdm)
  apply Fourier.boxIntegral_mono m
  intro v
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
    (norm_diagonal_invariantProductAmplitude_le hf hphase hHd hH hshift v)

end WaveTurbulence.Incoh
