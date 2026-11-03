/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.SobolevFourierRepresentation
public import WaveTurbulence.Foundations.WeylSums.ScaledSobolevCutoff

/-!
# Quantitative Fourier weights for the DH23 amplitude

Finite-order global derivative control of the amplitude and one fixed
compact cutoff give a Fourier coefficient norm `≤ C D width^(Fintype.card ι)`. The
constant is independent of the amplitude, center, and cutoff width.
-/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- The Fourier coefficient bound for a bounded finite-order amplitude
localized by a fixed compact cutoff. These are regularity and derivative
premises, rather than an assumed Fourier or exponential-sum estimate. -/
theorem exists_weighted_cutoff_fourier_bound {ι : Type*} [Fintype ι] {N : ℕ} (hN : Fintype.card ι < N)
    (κ : EuclideanSpace ℝ ι → ℂ) (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ N κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (width : ℝ), 1 ≤ width →
      ∀ (a : EuclideanSpace ℝ ι) (Φ : EuclideanSpace ℝ ι → ℂ),
      ContDiff ℝ N Φ → ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ D) →
      ∃ F : EuclideanSpace ℝ ι → ℂ, Integrable F ∧
        (∫ ξ, ‖F ξ‖) ≤ C*D*width^(Fintype.card ι) ∧
        ∀ x, Φ x*scaledTranslatedCutoff κ width a x = ∫ ξ, F ξ*e (∑ i, ξ i*x i) := by
  let K := Fourier.fourierL1Constant (EuclideanSpace ℝ ι) N
  let Q := ((N : ℝ)+1)*(2 : ℝ)^N
  let A := K*Q*Fourier.derivativeL1Sum N κ
  have hK : 0 ≤ K := Fourier.fourierL1Constant_nonneg N
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; exact mul_nonneg (mul_nonneg hK hQ) (Fourier.derivativeL1Sum_nonneg _ _)
  refine ⟨A+1, by positivity, ?_⟩
  intro width hw a Φ hΦ D hD hderiv
  have hwp : 0 < width := by linarith only [hw]
  let g := scaledTranslatedCutoff κ width a
  have hgc : HasCompactSupport g := scaledTranslatedCutoff_hasCompactSupport hκc hwp.ne' a
  have hgs : ContDiff ℝ N g := scaledTranslatedCutoff_contDiff hκs width a
  obtain ⟨F,hF,hbound,hrep⟩ := exists_sobolev_fourier_representation hN (fun x => Φ x*g x)
    hgc.mul_left (hΦ.mul hgs)
  refine ⟨F,hF,?_,hrep⟩
  calc
    _ ≤ K*Fourier.derivativeL1Sum N (fun x => Φ x*g x) := hbound
    _ ≤ K*(Q*D*Fourier.derivativeL1Sum N g) :=
      mul_le_mul_of_nonneg_left (derivativeL1Sum_mul_le Φ g hΦ hgs hgc hD hderiv) hK
    _ ≤ K*(Q*D*(width^(Fintype.card ι)*Fourier.derivativeL1Sum N κ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (derivativeL1Sum_scaledTranslated_le hκc hκs hw a) (mul_nonneg hQ hD)) hK
    _ = A*D*width^(Fintype.card ι) := by dsimp [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : A ≤ A+1) hD)
      (pow_nonneg hwp.le (Fintype.card ι))

end WaveTurbulence.WeylSums
