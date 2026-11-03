/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactFourier
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev

/-!
# Finite-order Fourier representations for the weighted minor-arc amplitude

DH23 Lemma 6.6 assumes bounds through order `10d`, rather than requiring
infinite differentiability of the amplitude. The representation below needs
only `N>dim`, preserves those finite-order premises, and displays the
quantitative Fourier coefficient norm.
-/

public section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace WaveTurbulence.WeylSums

/-- Finite-order compact Fourier inversion with its proved Sobolev constant. -/
theorem exists_sobolev_fourier_representation {ι : Type*} [Fintype ι] {N : ℕ} (hN : Fintype.card ι < N)
    (χ : EuclideanSpace ℝ ι → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ N χ) :
    ∃ F : EuclideanSpace ℝ ι → ℂ, Integrable F ∧
      (∫ ξ, ‖F ξ‖) ≤ Fourier.fourierL1Constant (EuclideanSpace ℝ ι) N *
        Fourier.derivativeL1Sum N χ ∧
      ∀ x, χ x = ∫ ξ, F ξ * e (∑ i, ξ i*x i) := by
  have hi (j : ℕ) (hj : j ≤ N) : Integrable (iteratedFDeriv ℝ j χ) :=
    (hs.continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) < N := by simpa using hN
  obtain ⟨hF,hbound⟩ := Fourier.fourier_integrable_and_integral_norm_le hdim hs hi
  have hχ : Integrable χ := hs.continuous.integrable_of_hasCompactSupport hc
  refine ⟨𝓕 χ,hF,hbound,?_⟩
  intro x
  have hinv := hχ.fourierInv_fourier_eq hF hs.continuous.continuousAt (v := x)
  rw [Real.fourierInv_eq'] at hinv
  simpa only [PiLp.inner_apply, Real.inner_apply, e, smul_eq_mul, mul_comm] using hinv.symm

end WaveTurbulence.WeylSums
