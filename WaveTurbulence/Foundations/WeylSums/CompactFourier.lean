/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CutoffFourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import WaveTurbulence.Foundations.Fourier.Chi0

/-! # Fourier representations for the joint cutoffs in the Weyl reduction -/

public section
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff
namespace WaveTurbulence.WeylSums

/-- The Fourier representation can be chosen Schwartz, so all the quantitative
compact-replacement tail bounds apply to this same weight. -/
theorem exists_schwartz_fourier_representation {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ∞ χ) :
    ∃ F : 𝓢(EuclideanSpace ℝ (Fin m), ℂ), ∀ x, χ x = ∫ ξ, F ξ * e (∑ i, ξ i * x i) := by
  let ψ : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) := hc.toSchwartzMap hs
  let F : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) := 𝓕 ψ
  refine ⟨F, ?_⟩
  intro x
  have hinv := ψ.integrable.fourierInv_fourier_eq
    (show Integrable (𝓕 (ψ : EuclideanSpace ℝ (Fin m) → ℂ)) from F.integrable)
    ψ.continuous.continuousAt (v := x)
  rw [Real.fourierInv_eq'] at hinv
  have hψ : ψ x = χ x := rfl
  rw [hψ] at hinv
  simpa only [F, SchwartzMap.fourier_coe, PiLp.inner_apply, Real.inner_apply,
    e, smul_eq_mul, mul_comm] using hinv.symm

/-- Every smooth compactly supported joint cutoff has an integrable Fourier
weight. This applies in dimensions `2d` and `3d`, including translated cutoffs. -/
theorem exists_compact_fourier_representation {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ∞ χ) :
    ∃ F : EuclideanSpace ℝ (Fin m) → ℂ, Integrable F ∧
      ∀ x, χ x = ∫ ξ, F ξ * e (∑ i, ξ i * x i) := by
  obtain ⟨F, hf⟩ := exists_schwartz_fourier_representation χ hc hs
  exact ⟨F, F.integrable, hf⟩

end WaveTurbulence.WeylSums
